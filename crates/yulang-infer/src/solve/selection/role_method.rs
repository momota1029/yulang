use std::collections::HashMap;

use crate::diagnostic::TypeErrorKind;
use crate::ids::{DefId, TypeVar};
use crate::simplify::compact::{CompactBounds, CompactType};
use crate::solve::{DeferredRoleMethodCall, Infer, RoleArgInfo, RoleMethodInfo};
use crate::symbols::Name;

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
        for call in calls {
            let Some(info) = self.role_methods.get(&call.name).cloned() else {
                continue;
            };
            let resolution = if call.name.0 == "cast" {
                self.resolve_cast_method_def(call.recv_tv, call.result_tv)
                    .map(RoleMethodResolution::Concrete)
                    .unwrap_or_else(|| {
                        resolve_role_method_call(self, &info, Some(call.recv_tv), &call.arg_tvs)
                    })
            } else {
                resolve_role_method_call(self, &info, Some(call.recv_tv), &call.arg_tvs)
            };
            report_role_method_resolution_error(self, &info, &resolution, call.result_tv);
            let def = resolution.concrete_def().unwrap_or(info.def);
            self.resolved_selections
                .borrow_mut()
                .insert(call.result_tv, def);
        }
    }
}

fn resolve_role_method_call(
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
        .map(|tv| super::concrete_tv_repr(infer, *tv, allow_boundary))
        .collect::<Option<Vec<_>>>()
    else {
        return RoleMethodResolution::Unresolved;
    };
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
        [candidate] => candidate
            .member_defs
            .get(&info.name)
            .copied()
            .or_else(|| info.has_default_body.then_some(info.def))
            .map(RoleMethodResolution::Concrete)
            .unwrap_or(RoleMethodResolution::Unresolved),
        [] if role_matches.is_empty() => RoleMethodResolution::Missing {
            args: render_concrete_role_args(&concrete_inputs),
        },
        [] => RoleMethodResolution::Unresolved,
        _ => RoleMethodResolution::Ambiguous {
            args: render_concrete_role_args(&concrete_inputs),
            candidates: matches.len(),
            previews: role_candidate_previews(matches),
        },
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
enum RoleMethodResolution {
    Concrete(DefId),
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
            RoleMethodResolution::Concrete(def) => Some(*def),
            _ => None,
        }
    }

    fn concrete_def(&self) -> Option<DefId> {
        self.def()
    }
}

fn report_role_method_resolution_error(
    infer: &Infer,
    info: &RoleMethodInfo,
    resolution: &RoleMethodResolution,
    result_tv: TypeVar,
) {
    match resolution {
        RoleMethodResolution::Missing { args } => infer.report_synthetic_type_error(
            TypeErrorKind::MissingImpl {
                role: path_string(&info.role),
                args: args.clone(),
            },
            format!("role method call {}", result_tv.0),
        ),
        RoleMethodResolution::Ambiguous {
            args,
            candidates,
            previews,
        } => infer.report_synthetic_type_error(
            TypeErrorKind::AmbiguousImpl {
                role: path_string(&info.role),
                args: args.clone(),
                candidates: *candidates,
                previews: previews.clone(),
            },
            format!("role method call {}", result_tv.0),
        ),
        RoleMethodResolution::Concrete(_) | RoleMethodResolution::Unresolved => {}
    }
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
) -> Option<Vec<TypeVar>> {
    let mut mapped = HashMap::<String, TypeVar>::new();
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
        mapped.insert(recv_name, recv_tv);
    }
    if let Some(sig) = info.sig.as_ref() {
        let mut sig_inputs = Vec::new();
        collect_sig_input_var_names(sig, &mut sig_inputs);
        for (arg_tv, sig_name) in remaining_arg_tvs.iter().zip(sig_inputs) {
            if let Some(name) = sig_name {
                mapped.entry(name).or_insert(*arg_tv);
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
        .map(|name| mapped.get(&name).copied())
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
