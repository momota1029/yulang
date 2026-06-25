use poly::expr::DefId;
use poly::types::BuiltinType;
use rowan::SyntaxNode;
use serde::{Deserialize, Serialize};
use sources::{Name, Path};

use crate::lowering::{self, SignatureEffectAtom, SignatureEffectRow, SignatureType, SignatureVar};
use crate::{
    ActMethodDecl, CompiledNamespaceMergeOutput, CompiledNamespaceSurface, CompiledNamespaceSymbol,
    CompiledNamespaceTypeKind, CompiledNamespaceTypeSymbol, CompiledNamespaceVisibility,
    CompiledRuntimeMergeOutput, ConstructorPayload, ConstructorPayloadItem,
    ConstructorRecordPayloadField, ModuleTable, ModuleTypeDecl, ModuleTypeKind, RoleMethodDecl,
    StoredSignature, TypeDeclId, TypeFieldMethodDecl, TypeMethodDecl, TypeMethodReceiver,
    namespace_path,
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
    pub act_templates: Vec<CompiledLoweringActTemplate>,
    pub constructor_payloads: Vec<CompiledLoweringConstructorPayload>,
    pub act_operations: Vec<CompiledLoweringActOperationSignature>,
    pub role_shapes: Vec<CompiledLoweringRoleShape>,
    pub type_methods: Vec<CompiledLoweringTypeMethod>,
    pub type_field_methods: Vec<CompiledLoweringTypeFieldMethod>,
    pub act_methods: Vec<CompiledLoweringActMethod>,
    pub role_methods: Vec<CompiledLoweringRoleMethodSignature>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompiledLoweringMergeError {
    MissingTypeSymbol { prefix: usize, symbol: u32 },
    MissingValueSymbol { prefix: usize, symbol: u32 },
    MissingDef { prefix: usize, def: DefId },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledLoweringActTypeVars {
    pub type_symbol: u32,
    pub type_path: Vec<String>,
    pub vars: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledLoweringActTemplate {
    pub type_symbol: u32,
    pub type_path: Vec<String>,
    pub source: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledLoweringConstructorPayload {
    pub value_symbol: u32,
    pub value_path: Vec<String>,
    pub owner_type_symbol: u32,
    pub owner_type_path: Vec<String>,
    pub owner_type_vars: Vec<String>,
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
    pub source_def: Option<DefId>,
    pub value_symbol: Option<u32>,
    pub value_path: Option<Vec<String>>,
    pub name: String,
    pub signature: Option<CompiledSignatureType>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledLoweringRoleShape {
    pub type_symbol: u32,
    pub type_path: Vec<String>,
    pub inputs: Vec<String>,
    pub associated: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledLoweringTypeMethod {
    pub owner_type_symbol: u32,
    pub owner_type_path: Vec<String>,
    pub source_def: DefId,
    pub value_symbol: Option<u32>,
    pub value_path: Option<Vec<String>>,
    pub name: String,
    pub receiver: String,
    pub receiver_kind: TypeMethodReceiver,
    pub visibility: CompiledNamespaceVisibility,
    pub order: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledLoweringTypeFieldMethod {
    pub owner_type_symbol: u32,
    pub owner_type_path: Vec<String>,
    pub source_def: DefId,
    pub name: String,
    pub receiver_kind: TypeMethodReceiver,
    pub visibility: CompiledNamespaceVisibility,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledLoweringActMethod {
    pub owner_type_symbol: u32,
    pub owner_type_path: Vec<String>,
    pub source_def: DefId,
    pub value_symbol: Option<u32>,
    pub value_path: Option<Vec<String>>,
    pub name: String,
    pub receiver: String,
    pub visibility: CompiledNamespaceVisibility,
    pub order: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledLoweringRoleMethodSignature {
    pub type_symbol: u32,
    pub type_path: Vec<String>,
    pub source_def: DefId,
    pub value_symbol: Option<u32>,
    pub value_path: Option<Vec<String>>,
    pub name: String,
    pub receiver: Option<String>,
    pub visibility: CompiledNamespaceVisibility,
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

        let mut act_templates = namespace
            .types
            .iter()
            .filter(|ty| ty.kind == CompiledNamespaceTypeKind::Act)
            .filter_map(|ty| {
                let decl = type_decl_for_namespace_path(modules, &ty.path)?;
                if decl.kind != ModuleTypeKind::Act {
                    return None;
                }
                let source = modules.act_template(decl.id)?.text().to_string();
                Some(CompiledLoweringActTemplate {
                    type_symbol: ty.unit_id,
                    type_path: ty.path.clone(),
                    source,
                })
            })
            .collect::<Vec<_>>();
        act_templates.sort_by_key(|entry| entry.type_symbol);

        let mut constructor_payloads = namespace
            .values
            .iter()
            .filter_map(|value| {
                let def = value_def_for_namespace_symbol(modules, namespace, value.unit_id)?;
                let constructor = modules.constructor_by_def(def)?;
                let owner = type_symbol_for_decl(modules, namespace, constructor.owner)?;
                Some(CompiledLoweringConstructorPayload {
                    value_symbol: value.unit_id,
                    value_path: value.path.clone(),
                    owner_type_symbol: owner.unit_id,
                    owner_type_path: owner.path,
                    owner_type_vars: constructor.type_vars.clone(),
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
                            let value =
                                act_operation_value_symbol(modules, namespace, &decl, &op.name);
                            let source_def = act_operation_source_def(modules, decl.id, &op.name);
                            Some(CompiledLoweringActOperationSignature {
                                type_symbol: ty.unit_id,
                                type_path: ty.path.clone(),
                                source_def,
                                value_symbol: value.as_ref().map(|value| value.unit_id),
                                value_path: value.map(|value| value.path),
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

        let mut role_shapes = namespace
            .types
            .iter()
            .filter(|ty| ty.kind == CompiledNamespaceTypeKind::Role)
            .filter_map(|ty| {
                let decl = type_decl_for_namespace_path(modules, &ty.path)?;
                if decl.kind != ModuleTypeKind::Role {
                    return None;
                }
                Some(CompiledLoweringRoleShape {
                    type_symbol: ty.unit_id,
                    type_path: ty.path.clone(),
                    inputs: modules.role_inputs(decl.id).to_vec(),
                    associated: modules.role_associated(decl.id).to_vec(),
                })
            })
            .collect::<Vec<_>>();
        role_shapes.sort_by_key(|entry| entry.type_symbol);

        let mut type_methods = modules
            .all_type_methods()
            .filter_map(|method| compile_type_method(modules, namespace, method))
            .collect::<Vec<_>>();
        type_methods.sort_by(|left, right| {
            (
                left.owner_type_symbol,
                left.order,
                &left.receiver,
                &left.name,
                left.receiver_kind as u8,
            )
                .cmp(&(
                    right.owner_type_symbol,
                    right.order,
                    &right.receiver,
                    &right.name,
                    right.receiver_kind as u8,
                ))
        });

        let mut type_field_methods = modules
            .all_type_field_methods()
            .filter_map(|method| compile_type_field_method(modules, namespace, method))
            .collect::<Vec<_>>();
        type_field_methods.sort_by(|left, right| {
            (
                left.owner_type_symbol,
                &left.name,
                left.receiver_kind as u8,
                left.source_def.0,
            )
                .cmp(&(
                    right.owner_type_symbol,
                    &right.name,
                    right.receiver_kind as u8,
                    right.source_def.0,
                ))
        });

        let mut act_methods = modules
            .all_act_methods()
            .filter_map(|method| compile_act_method(modules, namespace, method))
            .collect::<Vec<_>>();
        act_methods.sort_by(|left, right| {
            (
                left.owner_type_symbol,
                left.order,
                &left.receiver,
                &left.name,
            )
                .cmp(&(
                    right.owner_type_symbol,
                    right.order,
                    &right.receiver,
                    &right.name,
                ))
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
                            let value = value_symbol_for_def(modules, namespace, method.def);
                            Some(CompiledLoweringRoleMethodSignature {
                                type_symbol: ty.unit_id,
                                type_path: ty.path.clone(),
                                source_def: method.def,
                                value_symbol: value.as_ref().map(|value| value.unit_id),
                                value_path: value.map(|value| value.path),
                                name: method.name.0.clone(),
                                receiver: method.receiver.as_ref().map(|name| name.0.clone()),
                                visibility: compiled_visibility(method.vis),
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
            act_templates,
            constructor_payloads,
            act_operations,
            role_shapes,
            type_methods,
            type_field_methods,
            act_methods,
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

        for entry in &self.act_templates {
            let Some(decl) = type_decl_for_namespace_path(modules, &entry.type_path) else {
                continue;
            };
            if decl.kind != ModuleTypeKind::Act {
                continue;
            }
            let Some(template) = restore_compiled_act_template(&entry.source) else {
                continue;
            };
            modules.set_act_template(decl.id, template);
        }

        for entry in &self.constructor_payloads {
            let Some(def) = value_def_for_namespace_path(modules, &entry.value_path) else {
                continue;
            };
            let Some(payload) = restore_compiled_constructor_payload(modules, &entry.payload)
            else {
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
            let signature = restore_compiled_optional_stored_signature(modules, &entry.signature);
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
            let signature = restore_compiled_optional_stored_signature(modules, &entry.signature);
            if let Some(methods) = modules.role_methods.get_mut(&decl.id)
                && let Some(method) = methods.iter_mut().find(|method| {
                    method.name.0 == entry.name && method.order.index() == entry.order
                })
            {
                method.signature = signature;
            }
        }
    }

    pub fn merge_prefixes<'a>(
        prefixes: impl IntoIterator<Item = &'a CompiledLoweringSurface>,
        namespace: &CompiledNamespaceMergeOutput,
        runtime: &CompiledRuntimeMergeOutput,
    ) -> Result<Self, CompiledLoweringMergeError> {
        let mut merged = Self::default();
        for (prefix, surface) in prefixes.into_iter().enumerate() {
            for entry in &surface.act_type_vars {
                let mut entry = entry.clone();
                entry.type_symbol = remap_type_symbol(prefix, entry.type_symbol, namespace)?;
                merged.act_type_vars.push(entry);
            }
            for entry in &surface.act_templates {
                let mut entry = entry.clone();
                entry.type_symbol = remap_type_symbol(prefix, entry.type_symbol, namespace)?;
                merged.act_templates.push(entry);
            }
            for entry in &surface.constructor_payloads {
                let mut entry = entry.clone();
                entry.value_symbol = remap_value_symbol(prefix, entry.value_symbol, namespace)?;
                entry.owner_type_symbol =
                    remap_type_symbol(prefix, entry.owner_type_symbol, namespace)?;
                merged.constructor_payloads.push(entry);
            }
            for entry in &surface.act_operations {
                let mut entry = entry.clone();
                entry.type_symbol = remap_type_symbol(prefix, entry.type_symbol, namespace)?;
                entry.source_def = remap_optional_def(prefix, entry.source_def, runtime)?;
                entry.value_symbol =
                    remap_optional_value_symbol(prefix, entry.value_symbol, namespace)?;
                merged.act_operations.push(entry);
            }
            for entry in &surface.role_shapes {
                let mut entry = entry.clone();
                entry.type_symbol = remap_type_symbol(prefix, entry.type_symbol, namespace)?;
                merged.role_shapes.push(entry);
            }
            for entry in &surface.type_methods {
                let mut entry = entry.clone();
                entry.owner_type_symbol =
                    remap_type_symbol(prefix, entry.owner_type_symbol, namespace)?;
                entry.source_def = remap_def(prefix, entry.source_def, runtime)?;
                entry.value_symbol =
                    remap_optional_value_symbol(prefix, entry.value_symbol, namespace)?;
                merged.type_methods.push(entry);
            }
            for entry in &surface.type_field_methods {
                let mut entry = entry.clone();
                entry.owner_type_symbol =
                    remap_type_symbol(prefix, entry.owner_type_symbol, namespace)?;
                entry.source_def = remap_def(prefix, entry.source_def, runtime)?;
                merged.type_field_methods.push(entry);
            }
            for entry in &surface.act_methods {
                let mut entry = entry.clone();
                entry.owner_type_symbol =
                    remap_type_symbol(prefix, entry.owner_type_symbol, namespace)?;
                entry.source_def = remap_def(prefix, entry.source_def, runtime)?;
                entry.value_symbol =
                    remap_optional_value_symbol(prefix, entry.value_symbol, namespace)?;
                merged.act_methods.push(entry);
            }
            for entry in &surface.role_methods {
                let mut entry = entry.clone();
                entry.type_symbol = remap_type_symbol(prefix, entry.type_symbol, namespace)?;
                entry.source_def = remap_def(prefix, entry.source_def, runtime)?;
                entry.value_symbol =
                    remap_optional_value_symbol(prefix, entry.value_symbol, namespace)?;
                merged.role_methods.push(entry);
            }
        }
        sort_lowering_surface(&mut merged);
        Ok(merged)
    }
}

fn remap_type_symbol(
    prefix: usize,
    symbol: u32,
    namespace: &CompiledNamespaceMergeOutput,
) -> Result<u32, CompiledLoweringMergeError> {
    namespace
        .map_type(prefix, symbol)
        .ok_or(CompiledLoweringMergeError::MissingTypeSymbol { prefix, symbol })
}

fn remap_value_symbol(
    prefix: usize,
    symbol: u32,
    namespace: &CompiledNamespaceMergeOutput,
) -> Result<u32, CompiledLoweringMergeError> {
    namespace
        .map_value(prefix, symbol)
        .ok_or(CompiledLoweringMergeError::MissingValueSymbol { prefix, symbol })
}

fn remap_optional_value_symbol(
    prefix: usize,
    symbol: Option<u32>,
    namespace: &CompiledNamespaceMergeOutput,
) -> Result<Option<u32>, CompiledLoweringMergeError> {
    symbol
        .map(|symbol| remap_value_symbol(prefix, symbol, namespace))
        .transpose()
}

fn remap_def(
    prefix: usize,
    def: DefId,
    runtime: &CompiledRuntimeMergeOutput,
) -> Result<DefId, CompiledLoweringMergeError> {
    runtime
        .map_def(prefix, def)
        .ok_or(CompiledLoweringMergeError::MissingDef { prefix, def })
}

fn remap_optional_def(
    prefix: usize,
    def: Option<DefId>,
    runtime: &CompiledRuntimeMergeOutput,
) -> Result<Option<DefId>, CompiledLoweringMergeError> {
    def.map(|def| remap_def(prefix, def, runtime)).transpose()
}

fn sort_lowering_surface(surface: &mut CompiledLoweringSurface) {
    surface.act_type_vars.sort_by_key(|entry| entry.type_symbol);
    surface.act_templates.sort_by_key(|entry| entry.type_symbol);
    surface
        .constructor_payloads
        .sort_by_key(|entry| entry.value_symbol);
    surface.act_operations.sort_by(|left, right| {
        (left.type_symbol, &left.name).cmp(&(right.type_symbol, &right.name))
    });
    surface.role_shapes.sort_by_key(|entry| entry.type_symbol);
    surface.type_methods.sort_by(|left, right| {
        (
            left.owner_type_symbol,
            left.order,
            &left.receiver,
            &left.name,
            left.receiver_kind as u8,
        )
            .cmp(&(
                right.owner_type_symbol,
                right.order,
                &right.receiver,
                &right.name,
                right.receiver_kind as u8,
            ))
    });
    surface.type_field_methods.sort_by(|left, right| {
        (
            left.owner_type_symbol,
            &left.name,
            left.receiver_kind as u8,
            left.source_def.0,
        )
            .cmp(&(
                right.owner_type_symbol,
                &right.name,
                right.receiver_kind as u8,
                right.source_def.0,
            ))
    });
    surface.act_methods.sort_by(|left, right| {
        (
            left.owner_type_symbol,
            left.order,
            &left.receiver,
            &left.name,
        )
            .cmp(&(
                right.owner_type_symbol,
                right.order,
                &right.receiver,
                &right.name,
            ))
    });
    surface.role_methods.sort_by(|left, right| {
        (left.type_symbol, left.order, &left.name).cmp(&(
            right.type_symbol,
            right.order,
            &right.name,
        ))
    });
}

pub(crate) fn restore_compiled_act_template(source: &str) -> Option<crate::Cst> {
    let root = SyntaxNode::new_root(parser::parse_module_to_green(source));
    root.children()
        .find(|child| child.kind() == parser::lex::SyntaxKind::ActDecl)
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

fn compile_type_method(
    modules: &ModuleTable,
    namespace: &CompiledNamespaceSurface,
    method: &TypeMethodDecl,
) -> Option<CompiledLoweringTypeMethod> {
    let owner = type_symbol_for_decl(modules, namespace, method.owner)?;
    let value = value_symbol_for_def(modules, namespace, method.def);
    Some(CompiledLoweringTypeMethod {
        owner_type_symbol: owner.unit_id,
        owner_type_path: owner.path,
        source_def: method.def,
        value_symbol: value.as_ref().map(|value| value.unit_id),
        value_path: value.map(|value| value.path),
        name: method.name.0.clone(),
        receiver: method.receiver.0.clone(),
        receiver_kind: method.receiver_kind,
        visibility: compiled_visibility(method.vis),
        order: method.order.index(),
    })
}

fn compile_type_field_method(
    modules: &ModuleTable,
    namespace: &CompiledNamespaceSurface,
    method: &TypeFieldMethodDecl,
) -> Option<CompiledLoweringTypeFieldMethod> {
    let owner = type_symbol_for_decl(modules, namespace, method.owner)?;
    Some(CompiledLoweringTypeFieldMethod {
        owner_type_symbol: owner.unit_id,
        owner_type_path: owner.path,
        source_def: method.def,
        name: method.name.0.clone(),
        receiver_kind: method.receiver_kind,
        visibility: compiled_visibility(method.vis),
    })
}

fn compile_act_method(
    modules: &ModuleTable,
    namespace: &CompiledNamespaceSurface,
    method: &ActMethodDecl,
) -> Option<CompiledLoweringActMethod> {
    let owner = type_symbol_for_decl(modules, namespace, method.owner)?;
    let value = value_symbol_for_def(modules, namespace, method.def);
    Some(CompiledLoweringActMethod {
        owner_type_symbol: owner.unit_id,
        owner_type_path: owner.path,
        source_def: method.def,
        value_symbol: value.as_ref().map(|value| value.unit_id),
        value_path: value.map(|value| value.path),
        name: method.name.0.clone(),
        receiver: method.receiver.0.clone(),
        visibility: compiled_visibility(method.vis),
        order: method.order.index(),
    })
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

fn act_operation_source_def(
    modules: &ModuleTable,
    owner: TypeDeclId,
    name: &Name,
) -> Option<DefId> {
    modules
        .act_op_defs
        .iter()
        .find(|(_, op)| op.effect == owner && op.name == *name)
        .map(|(def, _)| *def)
}

fn compiled_visibility(vis: poly::expr::Vis) -> CompiledNamespaceVisibility {
    match vis {
        poly::expr::Vis::Pub => CompiledNamespaceVisibility::Pub,
        poly::expr::Vis::Our => CompiledNamespaceVisibility::Our,
        poly::expr::Vis::My => CompiledNamespaceVisibility::My,
    }
}

pub(crate) fn restore_compiled_constructor_payload(
    modules: &ModuleTable,
    payload: &CompiledConstructorPayload,
) -> Option<ConstructorPayload> {
    match payload {
        CompiledConstructorPayload::Unit => Some(ConstructorPayload::Unit),
        CompiledConstructorPayload::Tuple(items) => items
            .iter()
            .map(|item| {
                Some(ConstructorPayloadItem {
                    ty: restore_compiled_optional_stored_signature(modules, item),
                })
            })
            .collect::<Option<Vec<_>>>()
            .map(ConstructorPayload::Tuple),
        CompiledConstructorPayload::Record(fields) => fields
            .iter()
            .map(|field| {
                Some(ConstructorRecordPayloadField {
                    name: Name(field.name.clone()),
                    ty: restore_compiled_optional_stored_signature(modules, &field.ty),
                })
            })
            .collect::<Option<Vec<_>>>()
            .map(ConstructorPayload::Record),
    }
}

pub(crate) fn restore_compiled_optional_stored_signature(
    modules: &ModuleTable,
    signature: &Option<CompiledSignatureType>,
) -> Option<StoredSignature> {
    signature
        .as_ref()
        .and_then(|signature| restore_compiled_signature_type(modules, signature))
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

pub(crate) fn restore_compiled_signature_type(
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
            ret: Box::new(restore_compiled_signature_type(modules, ret)?),
        }),
        CompiledSignatureType::Tuple(items) => items
            .iter()
            .map(|item| restore_compiled_signature_type(modules, item))
            .collect::<Option<Vec<_>>>()
            .map(SignatureType::Tuple),
        CompiledSignatureType::Apply { callee, args } => Some(SignatureType::Apply {
            callee: Box::new(restore_compiled_signature_type(modules, callee)?),
            args: args
                .iter()
                .map(|arg| restore_compiled_signature_type(modules, arg))
                .collect::<Option<Vec<_>>>()?,
        }),
        CompiledSignatureType::Function {
            param,
            arg_eff,
            ret_eff,
            ret,
        } => Some(SignatureType::Function {
            param: Box::new(restore_compiled_signature_type(modules, param)?),
            arg_eff: match arg_eff {
                Some(row) => Some(restore_signature_effect_row(modules, row)?),
                None => None,
            },
            ret_eff: match ret_eff {
                Some(row) => Some(restore_signature_effect_row(modules, row)?),
                None => None,
            },
            ret: Box::new(restore_compiled_signature_type(modules, ret)?),
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
                    restore_compiled_signature_type(modules, ty)?,
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

fn type_symbol_for_decl(
    modules: &ModuleTable,
    namespace: &CompiledNamespaceSurface,
    id: TypeDeclId,
) -> Option<CompiledNamespaceTypeSymbol> {
    let decl = modules.type_decl_by_id(id)?;
    let path = namespace_path(&modules.type_decl_path(&decl));
    namespace.types.iter().find(|ty| ty.path == path).cloned()
}

fn act_operation_value_symbol(
    modules: &ModuleTable,
    namespace: &CompiledNamespaceSurface,
    decl: &ModuleTypeDecl,
    name: &Name,
) -> Option<CompiledNamespaceSymbol> {
    let companion = modules.type_companion(decl.id)?;
    let def = modules
        .value_decls(companion, name)
        .into_iter()
        .find(|candidate| {
            modules
                .act_op_defs
                .get(&candidate.def)
                .is_some_and(|op| op.effect == decl.id && op.name == *name)
        })
        .map(|candidate| candidate.def)?;
    value_symbol_for_def(modules, namespace, def)
}

fn value_symbol_for_def(
    modules: &ModuleTable,
    namespace: &CompiledNamespaceSurface,
    def: DefId,
) -> Option<CompiledNamespaceSymbol> {
    for module in &namespace.modules {
        let Some(live_module) = modules.module_by_path(&path_from_strings(&module.path)) else {
            continue;
        };
        for value in &module.values {
            let name = Name(value.name.clone());
            let matches_def = modules
                .value_decls(live_module, &name)
                .into_iter()
                .any(|decl| decl.order.index() == value.order && decl.def == def);
            if matches_def {
                return namespace
                    .values
                    .iter()
                    .find(|symbol| symbol.unit_id == value.symbol)
                    .cloned();
            }
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

    use crate::lowering::lower_loaded_files;
    use crate::{CompiledNamespaceSurface, CompiledRuntimeSurface};

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

    #[test]
    fn lowering_surface_merge_remaps_symbols_and_source_defs() {
        let left =
            compiled_lowering_surface(&["left"], "pub act signal 'a:\n  pub ping: () -> 'a\n");
        let right = compiled_lowering_surface(&["right"], "pub struct Box { value: int }\n");
        let namespace = CompiledNamespaceSurface::merge_prefixes_with_remap([
            &left.namespace,
            &right.namespace,
        ])
        .unwrap();
        let runtime = CompiledRuntimeSurface::merge_prefixes_with_remap(
            [&left.runtime, &right.runtime],
            &namespace,
        )
        .unwrap();
        let lowering = CompiledLoweringSurface::merge_prefixes(
            [&left.lowering, &right.lowering],
            &namespace,
            &runtime,
        )
        .unwrap();
        let namespace_index = crate::CompiledNamespaceIndex::new(&namespace.surface);
        let signal = namespace_index
            .exported_type_symbol(&["left".to_string()], "signal")
            .unwrap();
        let box_ctor = namespace_index
            .exported_value_symbol(&["right".to_string()], "Box")
            .unwrap();
        let source_ping = left
            .lowering
            .act_operations
            .iter()
            .find(|entry| entry.name == "ping")
            .and_then(|entry| entry.source_def)
            .unwrap();
        let merged_ping = lowering
            .act_operations
            .iter()
            .find(|entry| entry.name == "ping")
            .unwrap();

        assert!(
            lowering
                .act_type_vars
                .iter()
                .any(|entry| entry.type_symbol == signal)
        );
        assert!(
            lowering
                .act_templates
                .iter()
                .any(|entry| entry.type_symbol == signal)
        );
        assert!(
            lowering
                .constructor_payloads
                .iter()
                .any(|entry| entry.value_symbol == box_ctor)
        );
        assert_eq!(merged_ping.type_symbol, signal);
        assert_eq!(merged_ping.source_def, runtime.map_def(0, source_ping));
    }

    #[test]
    fn lowering_surface_merge_rejects_missing_type_symbol_remap() {
        let mut unit =
            compiled_lowering_surface(&["unit"], "pub act signal 'a:\n  pub ping: () -> 'a\n");
        unit.lowering.act_type_vars[0].type_symbol = u32::MAX;
        let namespace =
            CompiledNamespaceSurface::merge_prefixes_with_remap([&unit.namespace]).unwrap();
        let runtime =
            CompiledRuntimeSurface::merge_prefixes_with_remap([&unit.runtime], &namespace).unwrap();
        let error =
            match CompiledLoweringSurface::merge_prefixes([&unit.lowering], &namespace, &runtime) {
                Ok(_) => panic!("lowering merge should reject missing type symbol remap"),
                Err(error) => error,
            };

        assert_eq!(
            error,
            CompiledLoweringMergeError::MissingTypeSymbol {
                prefix: 0,
                symbol: u32::MAX,
            }
        );
    }

    struct LoweringSurfaceFixture {
        namespace: CompiledNamespaceSurface,
        lowering: CompiledLoweringSurface,
        runtime: CompiledRuntimeSurface,
    }

    fn compiled_lowering_surface(module: &[&str], text: &str) -> LoweringSurfaceFixture {
        assert_eq!(module.len(), 1);
        let root = format!("mod {};\n", module[0]);
        let loaded = sources::load(vec![source(&[], &root), source(module, text)]);
        let lowering = lower_loaded_files(&loaded).unwrap();
        let namespace = CompiledNamespaceSurface::from_module_table(&lowering.modules);
        let surface = CompiledLoweringSurface::from_module_table(&lowering.modules, &namespace);
        let runtime = CompiledRuntimeSurface::from_lowering_with_namespace(&lowering, &namespace);
        LoweringSurfaceFixture {
            namespace,
            lowering: surface,
            runtime,
        }
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
