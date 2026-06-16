//! Constructor payload lowering helpers.
//!
//! Constructor declarations need a small type-shape pass before expression
//! lowering can treat them as ordinary functions. This module keeps that
//! payload/signature wiring away from the main `ExprLowerer` control flow.

use super::*;

pub(super) enum ConstructorSignaturePayload {
    Unit,
    Tuple(Vec<ConstructorSignaturePayloadItem>),
    Record(Vec<ConstructorSignatureRecordPayloadField>),
}

pub(super) struct ConstructorSignaturePayloadItem {
    signature: Option<NegSignature>,
}

pub(super) struct ConstructorSignatureRecordPayloadField {
    name: Name,
    signature: Option<NegSignature>,
}

pub(super) enum ConstructorArg {
    Value {
        value: TypeVar,
        signature: Option<NegSignature>,
    },
    Record {
        value: TypeVar,
        fields: Vec<ConstructorRecordField>,
    },
}

impl ConstructorArg {
    pub(super) fn value(&self) -> TypeVar {
        match self {
            ConstructorArg::Value { value, .. } | ConstructorArg::Record { value, .. } => *value,
        }
    }
}

pub(super) struct ConstructorRecordField {
    name: String,
    value: TypeVar,
    signature: Option<NegSignature>,
}

pub(super) fn prepare_constructor_args(
    infer: &mut crate::Arena,
    payload: ConstructorSignaturePayload,
) -> Vec<ConstructorArg> {
    match payload {
        ConstructorSignaturePayload::Unit => Vec::new(),
        ConstructorSignaturePayload::Tuple(items) => items
            .into_iter()
            .map(|item| prepare_constructor_value_arg(infer, item))
            .collect(),
        ConstructorSignaturePayload::Record(fields) => {
            let record = infer.fresh_type_var();
            let fields = fields
                .into_iter()
                .map(|field| {
                    let value = infer.fresh_type_var();
                    ConstructorRecordField {
                        name: field.name.0,
                        value,
                        signature: field.signature,
                    }
                })
                .collect::<Vec<_>>();
            vec![ConstructorArg::Record {
                value: record,
                fields,
            }]
        }
    }
}

pub(super) fn prepare_constructor_pattern_args(
    infer: &mut crate::Arena,
    payload: ConstructorSignaturePayload,
    vars: &FxHashMap<String, TypeVar>,
) -> Vec<ConstructorArg> {
    match payload {
        ConstructorSignaturePayload::Unit => Vec::new(),
        ConstructorSignaturePayload::Tuple(items) => items
            .into_iter()
            .map(|item| prepare_constructor_pattern_value_arg(infer, item, vars))
            .collect(),
        ConstructorSignaturePayload::Record(fields) => {
            let record = infer.fresh_type_var();
            let fields = fields
                .into_iter()
                .map(|field| {
                    let value = field
                        .signature
                        .as_ref()
                        .and_then(|signature| signature_direct_var(signature.as_type()))
                        .and_then(|name| vars.get(name).copied())
                        .unwrap_or_else(|| infer.fresh_type_var());
                    ConstructorRecordField {
                        name: field.name.0,
                        value,
                        signature: field.signature,
                    }
                })
                .collect::<Vec<_>>();
            vec![ConstructorArg::Record {
                value: record,
                fields,
            }]
        }
    }
}

pub(super) fn constructor_payload_arity(payload: &ConstructorPayload) -> usize {
    match payload {
        ConstructorPayload::Unit => 0,
        ConstructorPayload::Tuple(items) => items.len(),
        ConstructorPayload::Record(_) => 1,
    }
}

pub(super) fn declared_constructor_expr_payloads(payloads: Vec<Cst>, arity: usize) -> Vec<Cst> {
    if arity == 1 || payloads.len() != 1 {
        return payloads;
    }

    let Some(group) = single_expr_paren_group_payload(&payloads[0]) else {
        return payloads;
    };
    let grouped = group
        .children()
        .filter(|child| child.kind() == SyntaxKind::Expr)
        .collect::<Vec<_>>();
    if grouped.len() == arity {
        grouped
    } else {
        payloads
    }
}

pub(super) fn constrain_constructor_arg_shapes(infer: &mut crate::Arena, args: &[ConstructorArg]) {
    for arg in args {
        let ConstructorArg::Record { value, fields } = arg else {
            continue;
        };
        let lower_fields = fields
            .iter()
            .map(|field| RecordField {
                name: field.name.clone(),
                value: infer.alloc_pos(Pos::Var(field.value)),
                optional: false,
            })
            .collect();
        let upper_fields = fields
            .iter()
            .map(|field| RecordField {
                name: field.name.clone(),
                value: infer.alloc_neg(Neg::Var(field.value)),
                optional: false,
            })
            .collect();
        let lower = infer.alloc_pos(Pos::Record(lower_fields));
        let upper = infer.alloc_neg(Neg::Record(upper_fields));
        let value_upper = infer.alloc_neg(Neg::Var(*value));
        let value_lower = infer.alloc_pos(Pos::Var(*value));
        infer.subtype(lower, value_upper);
        infer.subtype(value_lower, upper);
    }
}

pub(super) fn build_constructor_payload_signatures(
    payload: ConstructorPayload,
    builder: &NegSignatureBuilder,
) -> Result<ConstructorSignaturePayload, LoweringError> {
    match payload {
        ConstructorPayload::Unit => Ok(ConstructorSignaturePayload::Unit),
        ConstructorPayload::Tuple(items) => items
            .into_iter()
            .map(|item| {
                let signature = item
                    .ty
                    .map(|ty| builder.build_type_expr(&ty))
                    .transpose()
                    .map_err(|error| LoweringError::NegSignatureBuild { error })?;
                Ok(ConstructorSignaturePayloadItem { signature })
            })
            .collect::<Result<Vec<_>, LoweringError>>()
            .map(ConstructorSignaturePayload::Tuple),
        ConstructorPayload::Record(fields) => fields
            .into_iter()
            .map(|field| {
                let signature = field
                    .ty
                    .map(|ty| builder.build_type_expr(&ty))
                    .transpose()
                    .map_err(|error| LoweringError::NegSignatureBuild { error })?;
                Ok(ConstructorSignatureRecordPayloadField {
                    name: field.name,
                    signature,
                })
            })
            .collect::<Result<Vec<_>, LoweringError>>()
            .map(ConstructorSignaturePayload::Record),
    }
}

pub(super) fn connect_constructor_arg_signatures(
    infer: &mut crate::Arena,
    modules: &ModuleTable,
    vars: FxHashMap<String, TypeVar>,
    args: &[ConstructorArg],
) -> Result<(), LoweringError> {
    let mut lowerer = SignatureLowerer::with_vars(infer, modules, vars);
    for arg in args {
        match arg {
            ConstructorArg::Value {
                value,
                signature: Some(signature),
            } => {
                let lower = lowerer.alloc_pos(Pos::Var(*value));
                let upper = lowerer
                    .lower_data_neg(signature.as_type())
                    .map_err(|error| LoweringError::SignatureConstraint { error })?;
                lowerer.infer.subtype(lower, upper);
            }
            ConstructorArg::Value {
                signature: None, ..
            } => {}
            ConstructorArg::Record { fields, .. } => {
                for field in fields {
                    if let Some(signature) = &field.signature {
                        let lower = lowerer.alloc_pos(Pos::Var(field.value));
                        let upper = lowerer
                            .lower_data_neg(signature.as_type())
                            .map_err(|error| LoweringError::SignatureConstraint { error })?;
                        lowerer.infer.subtype(lower, upper);
                    }
                }
            }
        }
    }
    Ok(())
}

pub(super) fn connect_constructor_pattern_arg_signatures(
    infer: &mut crate::Arena,
    modules: &ModuleTable,
    vars: FxHashMap<String, TypeVar>,
    args: &[ConstructorArg],
) -> Result<(), LoweringError> {
    let mut lowerer = SignatureLowerer::with_vars(infer, modules, vars);
    for arg in args {
        match arg {
            ConstructorArg::Value {
                value,
                signature: Some(signature),
            } => {
                connect_constructor_pattern_value_signature(&mut lowerer, *value, signature)?;
            }
            ConstructorArg::Value {
                signature: None, ..
            } => {}
            ConstructorArg::Record { fields, .. } => {
                for field in fields {
                    if let Some(signature) = &field.signature {
                        connect_constructor_pattern_value_signature(
                            &mut lowerer,
                            field.value,
                            signature,
                        )?;
                    }
                }
            }
        }
    }
    Ok(())
}

fn single_expr_paren_group_payload(payload: &Cst) -> Option<Cst> {
    let children = payload.children().collect::<Vec<_>>();
    let [group] = children.as_slice() else {
        return None;
    };
    (group.kind() == SyntaxKind::Paren).then(|| group.clone())
}

fn prepare_constructor_value_arg(
    infer: &mut crate::Arena,
    item: ConstructorSignaturePayloadItem,
) -> ConstructorArg {
    let value = infer.fresh_type_var();
    ConstructorArg::Value {
        value,
        signature: item.signature,
    }
}

fn prepare_constructor_pattern_value_arg(
    infer: &mut crate::Arena,
    item: ConstructorSignaturePayloadItem,
    vars: &FxHashMap<String, TypeVar>,
) -> ConstructorArg {
    let value = item
        .signature
        .as_ref()
        .and_then(|signature| signature_direct_var(signature.as_type()))
        .and_then(|name| vars.get(name).copied())
        .unwrap_or_else(|| infer.fresh_type_var());
    ConstructorArg::Value {
        value,
        signature: item.signature,
    }
}

fn signature_direct_var(signature: &SignatureType) -> Option<&str> {
    match signature {
        SignatureType::Var(var) => Some(var.name.as_str()),
        _ => None,
    }
}

fn connect_constructor_pattern_value_signature(
    lowerer: &mut SignatureLowerer<'_>,
    value: TypeVar,
    signature: &NegSignature,
) -> Result<(), LoweringError> {
    let lower = lowerer
        .lower_data_pos(signature.as_type())
        .map_err(|error| LoweringError::SignatureConstraint { error })?;
    let value_upper = lowerer.alloc_neg(Neg::Var(value));
    lowerer.infer.subtype(lower, value_upper);

    let value_lower = lowerer.alloc_pos(Pos::Var(value));
    let upper = lowerer
        .lower_data_neg(signature.as_type())
        .map_err(|error| LoweringError::SignatureConstraint { error })?;
    lowerer.infer.subtype(value_lower, upper);
    Ok(())
}
