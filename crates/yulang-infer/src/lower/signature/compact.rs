use std::collections::{HashMap, HashSet};

use crate::ids::TypeVar;
use crate::lower::LowerState;
use crate::simplify::compact::{
    CompactBounds, CompactCon, CompactFun, CompactRecord, CompactRecordSpread, CompactRow,
    CompactType,
};
use crate::symbols::{Name, Path};
use crate::types::RecordField;

use super::lower::{canonical_sig_type_path, scoped_sig_prim_var, sig_var};
use super::{SigRow, SigType};

pub fn sig_type_head(sig: &SigType) -> Option<(Path, Vec<SigType>)> {
    match sig {
        SigType::Prim { path, .. } => Some((path.clone(), vec![])),
        SigType::Apply { path, args, .. } => Some((path.clone(), args.clone())),
        _ => None,
    }
}

pub fn compact_concrete_sig_type(sig: &SigType) -> Option<CompactType> {
    match sig {
        SigType::Prim { path, .. } => Some(CompactType {
            prims: std::collections::HashSet::from([path.clone()]),
            ..CompactType::default()
        }),
        SigType::Apply { path, args, .. } => Some(CompactType {
            cons: vec![CompactCon {
                path: path.clone(),
                args: args
                    .iter()
                    .map(|arg| {
                        let ty = compact_concrete_sig_type(arg)?;
                        Some(CompactBounds {
                            self_var: None,
                            lower: ty.clone(),
                            upper: ty,
                        })
                    })
                    .collect::<Option<Vec<_>>>()?,
            }],
            ..CompactType::default()
        }),
        SigType::Record { fields, .. } => Some(CompactType {
            records: vec![CompactRecord {
                fields: fields
                    .iter()
                    .map(|field| {
                        Some(RecordField {
                            name: field.name.clone(),
                            value: compact_concrete_sig_type(&field.ty)?,
                            optional: field.optional,
                        })
                    })
                    .collect::<Option<Vec<_>>>()?,
            }],
            ..CompactType::default()
        }),
        SigType::RecordTailSpread { fields, tail, .. } => Some(CompactType {
            record_spreads: vec![CompactRecordSpread {
                fields: fields
                    .iter()
                    .map(|field| {
                        Some(RecordField {
                            name: field.name.clone(),
                            value: compact_concrete_sig_type(&field.ty)?,
                            optional: field.optional,
                        })
                    })
                    .collect::<Option<Vec<_>>>()?,
                tail: Box::new(compact_concrete_sig_type(tail)?),
                tail_wins: false,
            }],
            ..CompactType::default()
        }),
        SigType::RecordHeadSpread { tail, fields, .. } => Some(CompactType {
            record_spreads: vec![CompactRecordSpread {
                fields: fields
                    .iter()
                    .map(|field| {
                        Some(RecordField {
                            name: field.name.clone(),
                            value: compact_concrete_sig_type(&field.ty)?,
                            optional: field.optional,
                        })
                    })
                    .collect::<Option<Vec<_>>>()?,
                tail: Box::new(compact_concrete_sig_type(tail)?),
                tail_wins: true,
            }],
            ..CompactType::default()
        }),
        SigType::Unit { .. } => Some(CompactType {
            prims: std::collections::HashSet::from([Path {
                segments: vec![Name("unit".to_string())],
            }]),
            ..CompactType::default()
        }),
        SigType::Tuple { items, .. } => Some(CompactType {
            tuples: vec![
                items
                    .iter()
                    .map(compact_concrete_sig_type)
                    .collect::<Option<Vec<_>>>()?,
            ],
            ..CompactType::default()
        }),
        SigType::Var(_) | SigType::Fun { .. } => None,
    }
}

pub fn render_concrete_sig_type(sig: &SigType) -> Option<String> {
    let ty = compact_concrete_sig_type(sig)?;
    Some(crate::display::format_coalesced_scheme(
        &crate::simplify::compact::CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: ty,
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        },
    ))
}

pub fn compact_sig_pattern_type(
    state: &LowerState,
    sig: &SigType,
    vars: &mut HashMap<String, TypeVar>,
) -> CompactType {
    match sig {
        SigType::Prim { path, span } => {
            if let Some(var) = scoped_sig_prim_var(path, *span, vars) {
                CompactType {
                    vars: std::collections::HashSet::from([sig_var(state, vars, &var)]),
                    ..CompactType::default()
                }
            } else {
                CompactType {
                    cons: vec![CompactCon {
                        path: canonical_sig_type_path(state, path),
                        args: Vec::new(),
                    }],
                    ..CompactType::default()
                }
            }
        }
        SigType::Apply { path, args, .. } => CompactType {
            cons: vec![CompactCon {
                path: canonical_sig_type_path(state, path),
                args: args
                    .iter()
                    .map(|arg| {
                        let ty = compact_sig_pattern_type(state, arg, vars);
                        CompactBounds {
                            self_var: None,
                            lower: ty.clone(),
                            upper: ty,
                        }
                    })
                    .collect(),
            }],
            ..CompactType::default()
        },
        SigType::Var(var) => CompactType {
            vars: std::collections::HashSet::from([sig_var(state, vars, var)]),
            ..CompactType::default()
        },
        SigType::Unit { .. } => CompactType {
            prims: std::collections::HashSet::from([Path {
                segments: vec![Name("unit".to_string())],
            }]),
            ..CompactType::default()
        },
        SigType::Tuple { items, .. } => CompactType {
            tuples: vec![
                items
                    .iter()
                    .map(|item| compact_sig_pattern_type(state, item, vars))
                    .collect(),
            ],
            ..CompactType::default()
        },
        SigType::Record { fields, .. } => CompactType {
            records: vec![CompactRecord {
                fields: fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: compact_sig_pattern_type(state, &field.ty, vars),
                        optional: field.optional,
                    })
                    .collect(),
            }],
            ..CompactType::default()
        },
        SigType::RecordTailSpread { fields, tail, .. } => CompactType {
            record_spreads: vec![CompactRecordSpread {
                fields: fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: compact_sig_pattern_type(state, &field.ty, vars),
                        optional: field.optional,
                    })
                    .collect(),
                tail: Box::new(compact_sig_pattern_type(state, tail, vars)),
                tail_wins: false,
            }],
            ..CompactType::default()
        },
        SigType::RecordHeadSpread { tail, fields, .. } => CompactType {
            record_spreads: vec![CompactRecordSpread {
                fields: fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: compact_sig_pattern_type(state, &field.ty, vars),
                        optional: field.optional,
                    })
                    .collect(),
                tail: Box::new(compact_sig_pattern_type(state, tail, vars)),
                tail_wins: true,
            }],
            ..CompactType::default()
        },
        SigType::Fun {
            arg, ret_eff, ret, ..
        } => CompactType {
            funs: vec![CompactFun {
                arg: compact_sig_pattern_type(state, arg, vars),
                arg_eff: CompactType::default(),
                ret_eff: ret_eff
                    .as_ref()
                    .map(|row| compact_sig_pattern_row(state, row, vars))
                    .unwrap_or_default(),
                ret: compact_sig_pattern_type(state, ret, vars),
            }],
            ..CompactType::default()
        },
    }
}

fn compact_sig_pattern_row(
    state: &LowerState,
    row: &SigRow,
    vars: &mut HashMap<String, TypeVar>,
) -> CompactType {
    CompactType {
        rows: vec![CompactRow {
            items: row
                .items
                .iter()
                .map(|item| compact_sig_pattern_type(state, item, vars))
                .collect(),
            tail: Box::new(row.tail.as_ref().map_or_else(CompactType::default, |tail| {
                CompactType {
                    vars: std::collections::HashSet::from([sig_var(state, vars, tail)]),
                    ..CompactType::default()
                }
            })),
        }],
        ..CompactType::default()
    }
}

pub fn collect_all_sig_vars(sig: &SigType, out: &mut HashSet<String>) {
    match sig {
        SigType::Var(var) => {
            out.insert(var.name.clone());
        }
        SigType::Apply { args, .. } => {
            for arg in args {
                collect_all_sig_vars(arg, out);
            }
        }
        SigType::Record { fields, .. } => {
            for field in fields {
                collect_all_sig_vars(&field.ty, out);
            }
        }
        SigType::Tuple { items, .. } => {
            for item in items {
                collect_all_sig_vars(item, out);
            }
        }
        SigType::RecordTailSpread { fields, tail, .. } => {
            for field in fields {
                collect_all_sig_vars(&field.ty, out);
            }
            collect_all_sig_vars(tail, out);
        }
        SigType::RecordHeadSpread { tail, fields, .. } => {
            collect_all_sig_vars(tail, out);
            for field in fields {
                collect_all_sig_vars(&field.ty, out);
            }
        }
        SigType::Fun {
            arg, ret_eff, ret, ..
        } => {
            collect_all_sig_vars(arg, out);
            if let Some(row) = ret_eff {
                for item in &row.items {
                    collect_all_sig_vars(item, out);
                }
                if let Some(tail) = &row.tail {
                    out.insert(tail.name.clone());
                }
            }
            collect_all_sig_vars(ret, out);
        }
        SigType::Prim { .. } | SigType::Unit { .. } => {}
    }
}
