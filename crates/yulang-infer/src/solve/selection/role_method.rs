use std::collections::HashMap;

use crate::ids::{DefId, TypeVar};
use crate::scheme::compact_pos_type;
use crate::simplify::compact::{
    CompactBounds, CompactCon, CompactFun, CompactRecord, CompactRecordSpread, CompactRow,
    CompactType, CompactTypeScheme, CompactVariant,
};
use crate::solve::role::role_method_info_for_path;
use crate::solve::{DeferredRoleMethodCall, Infer, RoleArgInfo, RoleMethodInfo};
use crate::symbols::Name;
use crate::types::{Neg, RecordField};

impl Infer {
    pub(crate) fn has_cast_role_method(&self) -> bool {
        self.role_methods.contains_key(&Name("cast".to_string()))
    }

    pub(crate) fn push_deferred_role_method_call(&self, call: DeferredRoleMethodCall) {
        self.deferred_role_method_calls.borrow_mut().push(call);
    }

    pub(crate) fn resolve_role_method_call_def(
        &self,
        info: &RoleMethodInfo,
        recv_tv: Option<TypeVar>,
        arg_tvs: &[TypeVar],
    ) -> Option<DefId> {
        resolve_role_method_call(self, info, recv_tv, arg_tvs).def()
    }

    pub(crate) fn resolve_concrete_role_method_call_def(
        &self,
        info: &RoleMethodInfo,
        recv_tv: Option<TypeVar>,
        arg_tvs: &[TypeVar],
    ) -> Option<DefId> {
        let def = self.resolve_role_method_call_def(info, recv_tv, arg_tvs)?;
        (!self.is_role_method_def(def)).then_some(def)
    }

    pub(crate) fn resolve_cast_method_def(
        &self,
        source_tv: TypeVar,
        target_tv: TypeVar,
    ) -> Option<DefId> {
        self.resolve_cast_method(source_tv, target_tv).def()
    }

    pub(crate) fn resolve_cast_method(
        &self,
        source_tv: TypeVar,
        target_tv: TypeVar,
    ) -> CastMethodResolution {
        let Some(info) = self.role_methods.get(&Name("cast".to_string())) else {
            return CastMethodResolution::Unresolved;
        };
        let arg_infos = self.role_arg_infos_of(&info.role);
        let mut indices = Vec::new();
        let mut concrete_args = Vec::new();
        for (index, arg_info) in arg_infos.iter().enumerate() {
            let tv = if arg_info.is_input {
                source_tv
            } else if arg_info.name == "to" {
                target_tv
            } else {
                continue;
            };
            indices.push(index);
            let concrete = if arg_info.is_input {
                super::compact_repr::concrete_tv_lower_repr(self, tv, true)
            } else {
                super::compact_repr::concrete_tv_upper_repr(self, tv, true)
            };
            let Some(concrete) = concrete else {
                return CastMethodResolution::Unresolved;
            };
            concrete_args.push(concrete);
        }
        if indices.len() < 2 {
            return CastMethodResolution::Unresolved;
        }
        if concrete_args.iter().any(|arg| !is_nominal_cast_arg(arg)) {
            return CastMethodResolution::Unresolved;
        }
        if concrete_args.len() >= 2 && concrete_args[0] == concrete_args[1] {
            return CastMethodResolution::Unresolved;
        }
        if concrete_args.len() >= 2 && same_nominal_cast_head(&concrete_args[0], &concrete_args[1])
        {
            return CastMethodResolution::Unresolved;
        }

        let candidates = self.role_impl_candidates_of(&info.role);
        let role_matches = candidates
            .iter()
            .filter(|candidate| {
                super::role_candidate_input_subst(candidate, &indices, &concrete_args).is_some()
            })
            .collect::<Vec<_>>();
        let matches = super::select_most_specific_role_candidates(
            role_matches.iter().copied().collect(),
            &indices,
        );
        match matches.as_slice() {
            [candidate] => candidate
                .member_defs
                .get(&info.name)
                .copied()
                .map(CastMethodResolution::Concrete)
                .unwrap_or(CastMethodResolution::Unresolved),
            [] if role_matches.is_empty() => CastMethodResolution::Missing {
                role: path_string(&info.role),
                args: render_concrete_role_args(&concrete_args),
            },
            [] => CastMethodResolution::Unresolved,
            _ => CastMethodResolution::Ambiguous {
                role: path_string(&info.role),
                args: render_concrete_role_args(&concrete_args),
                candidates: matches.len(),
                previews: role_candidate_previews(matches),
            },
        }
    }

    pub(crate) fn resolve_deferred_role_method_calls(&self) {
        let calls = self.deferred_role_method_calls.borrow().clone();
        let mut unresolved = Vec::new();
        for call in calls {
            let Some(info) = call
                .role_path
                .as_ref()
                .and_then(|path| role_method_info_for_path(&self.role_methods, path))
                .or_else(|| self.role_methods.get(&call.name).cloned())
            else {
                unresolved.push(call);
                continue;
            };
            if !call.cast_coercion
                && role_method_value_arg_count(&info)
                    .is_some_and(|arity| call.arg_tvs.len() < arity)
            {
                unresolved.push(call);
                continue;
            }
            let resolution = if call.cast_coercion {
                self.resolve_cast_method_def(call.recv_tv, call.result_tv)
                    .map(|def| RoleMethodResolution::Selected {
                        def: Some(def),
                        output: None,
                    })
                    .unwrap_or_else(|| {
                        resolve_role_method_call(self, &info, Some(call.recv_tv), &call.arg_tvs)
                    })
            } else {
                resolve_role_method_call(self, &info, Some(call.recv_tv), &call.arg_tvs)
            };
            if let RoleMethodResolution::Selected {
                output: Some(output),
                ..
            } = &resolution
            {
                self.constrain_role_method_call_output(output, call.result_tv);
            }
            if let Some(def) = resolution.concrete_def() {
                self.resolved_selections
                    .borrow_mut()
                    .insert(call.result_tv, def);
            }
            match resolution {
                RoleMethodResolution::Missing { args } => {
                    self.report_synthetic_type_error(
                        crate::diagnostic::TypeErrorKind::MissingImpl {
                            role: path_string(&info.role),
                            args,
                        },
                        format!("role method call {}", call.name.0),
                    );
                }
                RoleMethodResolution::Ambiguous {
                    args,
                    candidates,
                    previews,
                } => {
                    self.report_synthetic_type_error(
                        crate::diagnostic::TypeErrorKind::AmbiguousImpl {
                            role: path_string(&info.role),
                            args,
                            candidates,
                            previews,
                        },
                        format!("role method call {}", call.name.0),
                    );
                }
                RoleMethodResolution::Unresolved => unresolved.push(call),
                RoleMethodResolution::Selected { .. } => {}
            }
        }
        *self.deferred_role_method_calls.borrow_mut() = unresolved;
    }

    fn constrain_role_method_call_output(&self, output: &CompactType, result_tv: TypeVar) {
        let pos = compact_pos_type(&self.arena, output, &CompactTypeScheme::default(), false);
        self.constrain(pos, Neg::Var(result_tv));
    }
}

pub(super) fn resolve_role_method_call(
    infer: &Infer,
    info: &RoleMethodInfo,
    recv_tv: Option<TypeVar>,
    arg_tvs: &[TypeVar],
) -> RoleMethodResolution {
    let arg_infos = infer.role_arg_infos_of(&info.role);
    let input_indices = arg_infos
        .iter()
        .enumerate()
        .filter_map(|(index, info)| info.is_input.then_some(index))
        .collect::<Vec<_>>();
    let Some(role_input_tvs) = role_method_input_tvs(info, &arg_infos, recv_tv, arg_tvs) else {
        return RoleMethodResolution::Unresolved;
    };
    let allow_boundary = true;
    let Some(concrete_inputs) = role_input_tvs
        .iter()
        .map(|tvs| super::compact_repr::concrete_tv_lower_join_repr(infer, tvs, allow_boundary))
        .collect::<Option<Vec<_>>>()
    else {
        return RoleMethodResolution::Unresolved;
    };
    let diagnostic_ready = concrete_inputs
        .iter()
        .all(compact_type_has_no_open_type_vars);
    let candidates = infer.role_impl_candidates_of(&info.role);
    let role_matches = candidates
        .iter()
        .filter(|candidate| {
            super::role_candidate_input_subst(candidate, &input_indices, &concrete_inputs).is_some()
        })
        .collect::<Vec<_>>();
    let matches = super::select_most_specific_role_candidates(
        role_matches.iter().copied().collect(),
        &input_indices,
    );
    match matches.as_slice() {
        [candidate] => {
            let def = candidate
                .member_defs
                .get(&info.name)
                .copied()
                .or_else(|| info.has_default_body.then_some(info.def));
            let output = role_method_output_compact_type(
                candidate,
                &arg_infos,
                &input_indices,
                &concrete_inputs,
            );
            match (def, output) {
                (Some(def), output) => RoleMethodResolution::Selected {
                    def: Some(def),
                    output,
                },
                (None, Some(output)) => RoleMethodResolution::Selected {
                    def: None,
                    output: Some(output),
                },
                (None, None) => RoleMethodResolution::Unresolved,
            }
        }
        [] if role_matches.is_empty() && diagnostic_ready => RoleMethodResolution::Missing {
            args: render_concrete_role_args(&concrete_inputs),
        },
        [] => RoleMethodResolution::Unresolved,
        _ if diagnostic_ready => RoleMethodResolution::Ambiguous {
            args: render_concrete_role_args(&concrete_inputs),
            candidates: matches.len(),
            previews: role_candidate_previews(matches),
        },
        _ => RoleMethodResolution::Unresolved,
    }
}

fn is_nominal_cast_arg(arg: &CompactType) -> bool {
    arg.vars.is_empty()
        && arg.funs.is_empty()
        && arg.records.is_empty()
        && arg.record_spreads.is_empty()
        && arg.variants.is_empty()
        && arg.tuples.is_empty()
        && arg.rows.is_empty()
        && (arg.prims.len() + arg.cons.len() == 1)
        && arg
            .cons
            .iter()
            .all(|con| con.args.iter().all(|arg| arg.self_var.is_none()))
}

fn same_nominal_cast_head(source: &CompactType, target: &CompactType) -> bool {
    match (
        source.prims.len(),
        source.cons.len(),
        target.prims.len(),
        target.cons.len(),
    ) {
        (1, 0, 1, 0) => source.prims == target.prims,
        (0, 1, 0, 1) => source.cons[0].path == target.cons[0].path,
        _ => false,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CastMethodResolution {
    Concrete(DefId),
    Missing {
        role: String,
        args: Vec<String>,
    },
    Ambiguous {
        role: String,
        args: Vec<String>,
        candidates: usize,
        previews: Vec<String>,
    },
    Unresolved,
}

impl CastMethodResolution {
    pub(crate) fn def(&self) -> Option<DefId> {
        match self {
            CastMethodResolution::Concrete(def) => Some(*def),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum RoleMethodResolution {
    Selected {
        def: Option<DefId>,
        output: Option<CompactType>,
    },
    Missing {
        args: Vec<String>,
    },
    Ambiguous {
        args: Vec<String>,
        candidates: usize,
        previews: Vec<String>,
    },
    Unresolved,
}

impl RoleMethodResolution {
    fn def(&self) -> Option<DefId> {
        match self {
            RoleMethodResolution::Selected { def, .. } => *def,
            _ => None,
        }
    }

    pub(super) fn concrete_def(&self) -> Option<DefId> {
        self.def()
    }
}

pub(super) fn role_method_role_name(info: &RoleMethodInfo) -> String {
    path_string(&info.role)
}

fn compact_type_has_no_open_type_vars(ty: &CompactType) -> bool {
    ty.vars.is_empty()
        && ty.cons.iter().all(|con| {
            con.args.iter().all(|arg| {
                arg.self_var.is_none()
                    && compact_type_has_no_open_type_vars(&arg.lower)
                    && compact_type_has_no_open_type_vars(&arg.upper)
            })
        })
        && ty.funs.iter().all(|fun| {
            compact_type_has_no_open_type_vars(&fun.arg)
                && compact_type_has_no_open_type_vars(&fun.arg_eff)
                && compact_type_has_no_open_type_vars(&fun.ret_eff)
                && compact_type_has_no_open_type_vars(&fun.ret)
        })
        && ty.records.iter().all(|record| {
            record
                .fields
                .iter()
                .all(|field| compact_type_has_no_open_type_vars(&field.value))
        })
        && ty.record_spreads.iter().all(|record| {
            record
                .fields
                .iter()
                .all(|field| compact_type_has_no_open_type_vars(&field.value))
                && compact_type_has_no_open_type_vars(&record.tail)
        })
        && ty.variants.iter().all(|variant| {
            variant
                .items
                .iter()
                .all(|(_, items)| items.iter().all(compact_type_has_no_open_type_vars))
        })
        && ty
            .tuples
            .iter()
            .all(|items| items.iter().all(compact_type_has_no_open_type_vars))
        && ty.rows.iter().all(|row| {
            row.items.iter().all(compact_type_has_no_open_type_vars)
                && compact_type_has_no_open_type_vars(&row.tail)
        })
}

fn role_method_output_compact_type(
    candidate: &crate::solve::RoleImplCandidate,
    arg_infos: &[RoleArgInfo],
    input_indices: &[usize],
    concrete_inputs: &[CompactType],
) -> Option<CompactType> {
    let subst = super::role_candidate_input_subst(candidate, input_indices, concrete_inputs)?;
    let output_index = arg_infos
        .iter()
        .enumerate()
        .find_map(|(index, info)| (!info.is_input).then_some(index))?;
    candidate
        .compact_args
        .get(output_index)
        .map(|output| subst_compact_type_with_compact(output, &subst))
}

fn subst_compact_type_with_compact(
    ty: &CompactType,
    subst: &HashMap<TypeVar, CompactType>,
) -> CompactType {
    let mut out = CompactType::default();
    for var in &ty.vars {
        if let Some(replacement) = subst.get(var) {
            merge_compact_type(&mut out, replacement.clone());
        } else {
            out.vars.insert(*var);
        }
    }
    out.prims.extend(ty.prims.iter().cloned());
    out.cons.extend(ty.cons.iter().map(|con| {
        CompactCon {
            path: con.path.clone(),
            args: con
                .args
                .iter()
                .map(|arg| subst_compact_bounds_with_compact(arg, subst))
                .collect(),
        }
    }));
    out.funs.extend(ty.funs.iter().map(|fun| CompactFun {
        arg: subst_compact_type_with_compact(&fun.arg, subst),
        arg_eff: subst_compact_type_with_compact(&fun.arg_eff, subst),
        ret_eff: subst_compact_type_with_compact(&fun.ret_eff, subst),
        ret: subst_compact_type_with_compact(&fun.ret, subst),
    }));
    out.records.extend(ty.records.iter().map(|record| {
        CompactRecord {
            fields: record
                .fields
                .iter()
                .map(|field| RecordField {
                    name: field.name.clone(),
                    value: subst_compact_type_with_compact(&field.value, subst),
                    optional: field.optional,
                })
                .collect(),
        }
    }));
    out.record_spreads
        .extend(ty.record_spreads.iter().map(|spread| {
            CompactRecordSpread {
                fields: spread
                    .fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: subst_compact_type_with_compact(&field.value, subst),
                        optional: field.optional,
                    })
                    .collect(),
                tail: Box::new(subst_compact_type_with_compact(&spread.tail, subst)),
                tail_wins: spread.tail_wins,
            }
        }));
    out.variants.extend(ty.variants.iter().map(|variant| {
        CompactVariant {
            items: variant
                .items
                .iter()
                .map(|(name, payloads)| {
                    (
                        name.clone(),
                        payloads
                            .iter()
                            .map(|payload| subst_compact_type_with_compact(payload, subst))
                            .collect(),
                    )
                })
                .collect(),
        }
    }));
    out.tuples.extend(ty.tuples.iter().map(|items| {
        items
            .iter()
            .map(|item| subst_compact_type_with_compact(item, subst))
            .collect()
    }));
    out.rows.extend(ty.rows.iter().map(|row| {
        CompactRow {
            items: row
                .items
                .iter()
                .map(|item| subst_compact_type_with_compact(item, subst))
                .collect(),
            tail: Box::new(subst_compact_type_with_compact(&row.tail, subst)),
        }
    }));
    out
}

fn subst_compact_bounds_with_compact(
    bounds: &CompactBounds,
    subst: &HashMap<TypeVar, CompactType>,
) -> CompactBounds {
    if bounds.self_var.is_none()
        && bounds.lower == bounds.upper
        && let Some(var) = super::compact_var::single_compact_var(&bounds.lower)
        && let Some(replacement) = subst.get(&var)
    {
        return CompactBounds {
            self_var: None,
            lower: replacement.clone(),
            upper: replacement.clone(),
        };
    }
    CompactBounds {
        self_var: bounds.self_var,
        lower: subst_compact_type_with_compact(&bounds.lower, subst),
        upper: subst_compact_type_with_compact(&bounds.upper, subst),
    }
}

fn merge_compact_type(out: &mut CompactType, replacement: CompactType) {
    out.vars.extend(replacement.vars);
    out.prims.extend(replacement.prims);
    out.cons.extend(replacement.cons);
    out.funs.extend(replacement.funs);
    out.records.extend(replacement.records);
    out.record_spreads.extend(replacement.record_spreads);
    out.variants.extend(replacement.variants);
    out.tuples.extend(replacement.tuples);
    out.rows.extend(replacement.rows);
}

fn render_concrete_role_args(inputs: &[CompactType]) -> Vec<String> {
    inputs.iter().map(render_concrete_compact_type).collect()
}

fn render_concrete_compact_type(ty: &CompactType) -> String {
    crate::display::dump::format_compact_role_constraint_arg(&CompactBounds {
        self_var: None,
        lower: ty.clone(),
        upper: CompactType::default(),
    })
}

fn role_candidate_previews(candidates: Vec<&crate::solve::RoleImplCandidate>) -> Vec<String> {
    candidates
        .into_iter()
        .map(render_role_candidate_preview)
        .collect()
}

fn render_role_candidate_preview(candidate: &crate::solve::RoleImplCandidate) -> String {
    format!(
        "{}<{}>",
        path_string(&candidate.role),
        candidate.args.join(", ")
    )
}

fn path_string(path: &crate::symbols::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.clone())
        .collect::<Vec<_>>()
        .join("::")
}

fn role_method_input_tvs(
    info: &RoleMethodInfo,
    arg_infos: &[RoleArgInfo],
    recv_tv: Option<TypeVar>,
    arg_tvs: &[TypeVar],
) -> Option<Vec<Vec<TypeVar>>> {
    let mut mapped = HashMap::<String, Vec<TypeVar>>::new();
    let mut remaining_arg_tvs = arg_tvs;
    if info.has_receiver {
        let recv_tv = match recv_tv {
            Some(recv_tv) => recv_tv,
            None => {
                let (recv_tv, rest) = arg_tvs.split_first()?;
                remaining_arg_tvs = rest;
                *recv_tv
            }
        };
        let recv_name = arg_infos.iter().find(|info| info.is_input)?.name.clone();
        mapped.entry(recv_name).or_default().push(recv_tv);
    }
    if let Some(sig) = info.sig.as_ref() {
        let mut sig_inputs = Vec::new();
        collect_sig_input_var_names(sig, &mut sig_inputs);
        for (arg_tv, sig_name) in remaining_arg_tvs.iter().zip(sig_inputs) {
            if let Some(name) = sig_name {
                mapped.entry(name).or_default().push(*arg_tv);
            }
        }
    }
    let input_names = arg_infos
        .iter()
        .filter(|info| info.is_input)
        .map(|info| info.name.clone())
        .collect::<Vec<_>>();
    input_names
        .into_iter()
        .map(|name| mapped.get(&name).cloned())
        .collect()
}

fn collect_sig_input_var_names(
    sig: &crate::lower::signature::SigType,
    out: &mut Vec<Option<String>>,
) {
    match sig {
        crate::lower::signature::SigType::Fun { arg, ret, .. } => {
            out.push(sig_var_name(arg));
            collect_sig_input_var_names(ret, out);
        }
        _ => {}
    }
}

fn sig_var_name(sig: &crate::lower::signature::SigType) -> Option<String> {
    match sig {
        crate::lower::signature::SigType::Var(var) => Some(var.name.clone()),
        _ => None,
    }
}

fn role_method_value_arg_count(info: &RoleMethodInfo) -> Option<usize> {
    info.sig.as_ref().map(count_sig_value_args)
}

fn count_sig_value_args(sig: &crate::lower::signature::SigType) -> usize {
    match sig {
        crate::lower::signature::SigType::Fun { ret, .. } => 1 + count_sig_value_args(ret),
        _ => 0,
    }
}
