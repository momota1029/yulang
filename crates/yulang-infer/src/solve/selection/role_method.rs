use std::collections::{HashMap, VecDeque};

use crate::ids::{DefId, NegId, PosId, TypeVar};
use crate::lower::builtin_types::can_runtime_coerce_primitive_type_paths;
use crate::scheme::compact_pos_type;
use crate::simplify::compact::{
    CompactBounds, CompactCon, CompactFun, CompactRecord, CompactRecordSpread, CompactRow,
    CompactType, CompactTypeScheme, CompactVariant,
};
use crate::solve::role::role_method_info_for_path;
use crate::solve::{
    DeferredRoleMethodCall, Infer, RoleArgInfo, RoleConstraint, RoleConstraintArg,
    RoleImplCandidate, RoleMethodInfo,
};
use crate::symbols::Name;
use crate::types::{Neg, Pos, RecordField};

impl Infer {
    pub(crate) fn has_cast_role_method(&self) -> bool {
        self.role_methods.contains_key(&Name("cast".to_string()))
    }

    pub(crate) fn push_deferred_role_method_call(&self, call: DeferredRoleMethodCall) {
        if let Some(info) = role_method_info_for_call(self, &call)
            && let Some(owner) = call.owner
        {
            self.add_role_method_call_constraint_for_owner(
                &info,
                owner,
                call.recv_tv,
                &call.arg_tvs,
                call.result_tv,
            );
        }
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
        let Some(args) = cast_method_args_from_tvs(self, &arg_infos, source_tv, target_tv) else {
            return CastMethodResolution::Unresolved;
        };
        resolve_cast_method_from_concrete_args(self, info, args)
    }

    pub(crate) fn resolve_cast_method_from_pos_neg(
        &self,
        source_pos: PosId,
        target_neg: NegId,
    ) -> CastMethodResolution {
        let Some(info) = self.role_methods.get(&Name("cast".to_string())) else {
            return CastMethodResolution::Unresolved;
        };
        let arg_infos = self.role_arg_infos_of(&info.role);
        let Some(args) = cast_method_args_from_pos_neg(self, &arg_infos, source_pos, target_neg)
        else {
            return CastMethodResolution::Unresolved;
        };
        resolve_cast_method_from_concrete_args(self, info, args)
    }

    pub(crate) fn resolve_deferred_role_method_calls(&self) {
        let calls = self.deferred_role_method_calls.borrow().clone();
        let mut unresolved = Vec::new();
        for call in calls {
            let Some(info) = role_method_info_for_call(self, &call) else {
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
                RoleMethodResolution::Unresolved => {
                    if let Some(owner) = call.owner {
                        self.add_role_method_call_constraint_for_owner(
                            &info,
                            owner,
                            call.recv_tv,
                            &call.arg_tvs,
                            call.result_tv,
                        );
                    }
                    unresolved.push(call);
                }
                RoleMethodResolution::Selected { .. } => {}
            }
        }
        *self.deferred_role_method_calls.borrow_mut() = unresolved;
    }

    pub(crate) fn add_deferred_role_method_constraints_for_owner(&self, owner: DefId) {
        let calls = self.deferred_role_method_calls.borrow().clone();
        for call in calls {
            if call.owner != Some(owner) {
                continue;
            }
            let Some(info) = role_method_info_for_call(self, &call) else {
                continue;
            };
            self.add_role_method_call_constraint_for_owner(
                &info,
                owner,
                call.recv_tv,
                &call.arg_tvs,
                call.result_tv,
            );
        }
    }

    pub(crate) fn has_deferred_role_method_call_for_owner(&self, owner: DefId) -> bool {
        self.deferred_role_method_calls.borrow().iter().any(|call| {
            if call.owner != Some(owner) {
                return false;
            }
            let Some(info) = role_method_info_for_call(self, call) else {
                return false;
            };
            call.cast_coercion
                || role_method_value_arg_count(&info).is_none_or(|arity| {
                    call.arg_tvs.len() >= arity
                        || partial_role_method_arg_tvs(self, &info, &call.arg_tvs, call.result_tv)
                            .len()
                            >= arity
                })
        })
    }

    pub(crate) fn add_role_method_call_constraint_for_owner(
        &self,
        info: &RoleMethodInfo,
        owner: crate::ids::DefId,
        recv_tv: TypeVar,
        arg_tvs: &[TypeVar],
        result_tv: TypeVar,
    ) {
        let arg_tvs = partial_role_method_arg_tvs(self, info, arg_tvs, result_tv);
        if role_method_value_arg_count(info).is_some_and(|arity| arg_tvs.len() < arity) {
            return;
        }
        let Some(constraint) = self.role_method_call_constraint(info, recv_tv, &arg_tvs, result_tv)
        else {
            return;
        };
        self.add_role_constraint(owner, constraint);
    }

    fn role_method_call_constraint(
        &self,
        info: &RoleMethodInfo,
        recv_tv: TypeVar,
        arg_tvs: &[TypeVar],
        result_tv: TypeVar,
    ) -> Option<RoleConstraint> {
        let arg_infos = self.role_arg_infos_of(&info.role);
        let input_map = role_method_input_tv_map(info, &arg_infos, Some(recv_tv), arg_tvs)?;
        let mut args = Vec::with_capacity(arg_infos.len());
        for arg_info in &arg_infos {
            let arg = if arg_info.is_input {
                role_constraint_arg_for_tvs(self, input_map.get(&arg_info.name)?)?
            } else if info.output_name.as_deref() == Some(arg_info.name.as_str()) {
                role_constraint_arg_for_tvs(self, &[result_tv])?
            } else {
                return None;
            };
            args.push(arg);
        }
        Some(RoleConstraint {
            role: info.role.clone(),
            args,
        })
    }

    fn constrain_role_method_call_output(&self, output: &CompactType, result_tv: TypeVar) {
        let pos = compact_pos_type(&self.arena, output, &CompactTypeScheme::default(), false);
        self.constrain(pos, Neg::Var(result_tv));
    }
}

fn role_constraint_arg_for_tvs(infer: &Infer, tvs: &[TypeVar]) -> Option<RoleConstraintArg> {
    let (&first, rest) = tvs.split_first()?;
    let mut pos = infer.alloc_pos(Pos::Var(first));
    let mut neg = infer.alloc_neg(Neg::Var(first));
    for &tv in rest {
        let rhs_pos = infer.alloc_pos(Pos::Var(tv));
        pos = infer.alloc_pos(Pos::Union(pos, rhs_pos));
        let rhs_neg = infer.alloc_neg(Neg::Var(tv));
        neg = infer.alloc_neg(Neg::Intersection(neg, rhs_neg));
    }
    Some(RoleConstraintArg { pos, neg })
}

fn partial_role_method_arg_tvs(
    infer: &Infer,
    info: &RoleMethodInfo,
    arg_tvs: &[TypeVar],
    result_tv: TypeVar,
) -> Vec<TypeVar> {
    let Some(arity) = role_method_value_arg_count(info) else {
        return arg_tvs.to_vec();
    };
    let mut out = arg_tvs.to_vec();
    let mut current = result_tv;
    while out.len() < arity {
        let Some((param, ret)) = function_value_var_parts(infer, current) else {
            break;
        };
        out.push(param);
        current = ret;
    }
    out
}

fn function_value_var_parts(infer: &Infer, tv: TypeVar) -> Option<(TypeVar, TypeVar)> {
    for lower in infer.lower_refs_of(tv) {
        let Pos::Fun { arg, ret, .. } = infer.arena.get_pos(lower) else {
            continue;
        };
        let Neg::Var(param) = infer.arena.get_neg(arg) else {
            continue;
        };
        let Pos::Var(ret) = infer.arena.get_pos(ret) else {
            continue;
        };
        return Some((param, ret));
    }
    for upper in infer.upper_refs_of(tv) {
        let Neg::Fun { arg, ret, .. } = infer.arena.get_neg(upper) else {
            continue;
        };
        let Pos::Var(param) = infer.arena.get_pos(arg) else {
            continue;
        };
        let Neg::Var(ret) = infer.arena.get_neg(ret) else {
            continue;
        };
        return Some((param, ret));
    }
    None
}

fn role_method_info_for_call(
    infer: &Infer,
    call: &DeferredRoleMethodCall,
) -> Option<RoleMethodInfo> {
    match &call.role_path {
        Some(path) => role_method_info_for_path(&infer.role_methods, path),
        None => infer.role_methods.get(&call.name).cloned(),
    }
}

fn cast_method_args_from_tvs(
    infer: &Infer,
    arg_infos: &[RoleArgInfo],
    source_tv: TypeVar,
    target_tv: TypeVar,
) -> Option<CastMethodArgs> {
    let mut indices = Vec::new();
    let mut concrete_args = Vec::new();
    let mut source_index = None;
    let mut target_index = None;
    for (index, arg_info) in arg_infos.iter().enumerate() {
        let tv = if arg_info.is_input {
            source_index = Some(index);
            source_tv
        } else if arg_info.name == "to" {
            target_index = Some(index);
            target_tv
        } else {
            continue;
        };
        indices.push(index);
        let concrete = if arg_info.is_input {
            super::compact_repr::concrete_tv_lower_repr(infer, tv, true)
        } else {
            super::compact_repr::concrete_tv_upper_repr(infer, tv, true)
        };
        let Some(concrete) = concrete else {
            return None;
        };
        concrete_args.push(concrete);
    }
    Some(CastMethodArgs {
        indices,
        concrete_args,
        source_index,
        target_index,
    })
}

fn cast_method_args_from_pos_neg(
    infer: &Infer,
    arg_infos: &[RoleArgInfo],
    source_pos: PosId,
    target_neg: NegId,
) -> Option<CastMethodArgs> {
    let mut indices = Vec::new();
    let mut concrete_args = Vec::new();
    let mut source_index = None;
    let mut target_index = None;
    for (index, arg_info) in arg_infos.iter().enumerate() {
        let concrete = if arg_info.is_input {
            source_index = Some(index);
            super::compact_repr::concrete_pos_repr(infer, source_pos, true)
        } else if arg_info.name == "to" {
            target_index = Some(index);
            super::compact_repr::concrete_neg_repr(infer, target_neg, true)
        } else {
            continue;
        };
        let concrete = concrete?;
        indices.push(index);
        concrete_args.push(concrete);
    }
    Some(CastMethodArgs {
        indices,
        concrete_args,
        source_index,
        target_index,
    })
}

fn resolve_cast_method_from_concrete_args(
    infer: &Infer,
    info: &RoleMethodInfo,
    args: CastMethodArgs,
) -> CastMethodResolution {
    if args.indices.len() < 2 {
        return CastMethodResolution::Unresolved;
    }
    if args
        .concrete_args
        .iter()
        .any(|arg| !is_nominal_cast_arg(arg))
    {
        return CastMethodResolution::Unresolved;
    }
    if args.concrete_args.len() >= 2 && args.concrete_args[0] == args.concrete_args[1] {
        return CastMethodResolution::Unresolved;
    }
    if args.concrete_args.len() >= 2
        && same_nominal_cast_head(&args.concrete_args[0], &args.concrete_args[1])
    {
        return CastMethodResolution::Unresolved;
    }
    if runtime_primitive_coercion_cast_args(&args) {
        return CastMethodResolution::Unresolved;
    }

    let candidates = infer.role_impl_candidates_of(&info.role);
    let role_matches = candidates
        .iter()
        .filter(|candidate| {
            super::role_candidate_input_subst(candidate, &args.indices, &args.concrete_args)
                .is_some()
        })
        .collect::<Vec<_>>();
    let matches = super::select_most_specific_role_candidates(
        role_matches.iter().copied().collect(),
        &args.indices,
    );
    match matches.as_slice() {
        [candidate] => candidate
            .member_defs
            .get(&info.name)
            .copied()
            .map(CastMethodResolution::Concrete)
            .unwrap_or(CastMethodResolution::Unresolved),
        [] if role_matches.is_empty() => {
            let has_cast_chain = args
                .source_index
                .zip(args.target_index)
                .and_then(|(source_index, target_index)| {
                    let source =
                        concrete_arg_for_index(&args.indices, &args.concrete_args, source_index)?;
                    let target =
                        concrete_arg_for_index(&args.indices, &args.concrete_args, target_index)?;
                    Some(has_transitive_cast_path(
                        &candidates,
                        source_index,
                        target_index,
                        source,
                        target,
                    ))
                })
                .unwrap_or(false);
            if has_cast_chain {
                CastMethodResolution::Unresolved
            } else {
                CastMethodResolution::Missing {
                    role: path_string(&info.role),
                    args: render_concrete_role_args(&args.concrete_args),
                }
            }
        }
        [] => CastMethodResolution::Unresolved,
        _ => CastMethodResolution::Ambiguous {
            role: path_string(&info.role),
            args: render_concrete_role_args(&args.concrete_args),
            candidates: matches.len(),
            previews: role_candidate_previews(matches),
        },
    }
}

fn runtime_primitive_coercion_cast_args(args: &CastMethodArgs) -> bool {
    let Some((source_index, target_index)) = args.source_index.zip(args.target_index) else {
        return false;
    };
    let Some(source) = concrete_arg_for_index(&args.indices, &args.concrete_args, source_index)
    else {
        return false;
    };
    let Some(target) = concrete_arg_for_index(&args.indices, &args.concrete_args, target_index)
    else {
        return false;
    };
    let Some(source) = single_nominal_cast_path(source) else {
        return false;
    };
    let Some(target) = single_nominal_cast_path(target) else {
        return false;
    };
    can_runtime_coerce_primitive_type_paths(source, target)
}

struct CastMethodArgs {
    indices: Vec<usize>,
    concrete_args: Vec<CompactType>,
    source_index: Option<usize>,
    target_index: Option<usize>,
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
                info,
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

fn concrete_arg_for_index<'a>(
    indices: &[usize],
    concrete_args: &'a [CompactType],
    index: usize,
) -> Option<&'a CompactType> {
    indices
        .iter()
        .position(|candidate| *candidate == index)
        .and_then(|arg_index| concrete_args.get(arg_index))
}

fn has_transitive_cast_path(
    candidates: &[RoleImplCandidate],
    source_index: usize,
    target_index: usize,
    source: &CompactType,
    target: &CompactType,
) -> bool {
    let edges = candidates
        .iter()
        .filter_map(|candidate| {
            let source = candidate.compact_args.get(source_index)?.clone();
            let target = candidate.compact_args.get(target_index)?.clone();
            (is_nominal_cast_arg(&source) && is_nominal_cast_arg(&target))
                .then_some((source, target))
        })
        .collect::<Vec<_>>();
    let mut seen = Vec::new();
    let mut queue = VecDeque::from([source.clone()]);

    while let Some(current) = queue.pop_front() {
        if seen.contains(&current) {
            continue;
        }
        seen.push(current.clone());
        for (from, to) in &edges {
            if from != &current {
                continue;
            }
            if to == target {
                return true;
            }
            if !seen.contains(to) {
                queue.push_back(to.clone());
            }
        }
    }
    false
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

fn single_nominal_cast_path(arg: &CompactType) -> Option<&crate::symbols::Path> {
    if !is_nominal_cast_arg(arg) {
        return None;
    }
    if arg.prims.len() == 1 && arg.cons.is_empty() {
        return arg.prims.iter().next();
    }
    if arg.prims.is_empty() && arg.cons.len() == 1 && arg.cons[0].args.is_empty() {
        return Some(&arg.cons[0].path);
    }
    None
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
    info: &RoleMethodInfo,
    candidate: &crate::solve::RoleImplCandidate,
    arg_infos: &[RoleArgInfo],
    input_indices: &[usize],
    concrete_inputs: &[CompactType],
) -> Option<CompactType> {
    let output_name = info.output_name.as_deref()?;
    let subst = super::role_candidate_input_subst(candidate, input_indices, concrete_inputs)?;
    let output_index = arg_infos
        .iter()
        .enumerate()
        .find_map(|(index, info)| (!info.is_input && info.name == output_name).then_some(index))?;
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
    let mapped = role_method_input_tv_map(info, arg_infos, recv_tv, arg_tvs)?;
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

fn role_method_input_tv_map(
    info: &RoleMethodInfo,
    arg_infos: &[RoleArgInfo],
    recv_tv: Option<TypeVar>,
    arg_tvs: &[TypeVar],
) -> Option<HashMap<String, Vec<TypeVar>>> {
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
    for (arg_tv, sig_name) in remaining_arg_tvs.iter().zip(&info.input_names) {
        if let Some(name) = sig_name {
            mapped.entry(name.clone()).or_default().push(*arg_tv);
        }
    }
    Some(mapped)
}

fn role_method_value_arg_count(info: &RoleMethodInfo) -> Option<usize> {
    Some(info.input_names.len())
}
