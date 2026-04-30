use crate::profile::ProfileClock as Instant;
use std::collections::HashMap;

use yulang_parser::lex::SyntaxKind;

use super::ActCopy;
use crate::ids::DefId;
use crate::lower::LowerState;
use crate::scheme::{
    freeze_type_var_with_non_generic, instantiate_frozen_scheme, subst_neg_id, subst_pos_id,
};
use crate::symbols::{Name, Path};
use crate::types::{Neg, Pos};

pub(crate) fn lower_act_copy_body(
    state: &mut LowerState,
    copy: ActCopy,
    dest_path: &Path,
    dest_args: &[(crate::ids::TypeVar, crate::ids::TypeVar)],
) {
    let start = Instant::now();
    let lowered = try_copy_lowered_act_body(state, &copy, dest_path, dest_args);
    if !lowered {
        let from_template = try_lower_act_copy_from_template(state, &copy, dest_path, dest_args);
        if !from_template {
            copy_effect_ops_from_source_module(state, &copy, dest_path, dest_args);
        }
    }
    state.lower_detail.lower_act_copy_body += start.elapsed();
}

fn try_lower_act_copy_from_template(
    state: &mut LowerState,
    copy: &ActCopy,
    dest_path: &Path,
    dest_args: &[(crate::ids::TypeVar, crate::ids::TypeVar)],
) -> bool {
    let start = Instant::now();
    let template = state
        .act_templates
        .get(&copy.source_path)
        .cloned()
        .or_else(|| {
            copy.source_path.segments.last().and_then(|name| {
                state
                    .act_templates
                    .get(&Path {
                        segments: vec![name.clone()],
                    })
                    .cloned()
            })
        });
    let Some(template) = template else {
        return false;
    };

    let source_names = crate::lower::signature::act_type_param_names(&template);
    if source_names.len() != copy.source_args.len() {
        return false;
    }

    let source_scope = source_names
        .into_iter()
        .zip(copy.source_args.iter())
        .map(|(name, (pos, _))| (name, *pos))
        .collect::<HashMap<_, _>>();
    let act_arg_tvs = dest_args.iter().map(|(pos, _)| *pos).collect::<Vec<_>>();
    let Some(body) = super::super::child_node(&template, SyntaxKind::IndentBlock)
        .or_else(|| super::super::child_node(&template, SyntaxKind::BraceGroup))
    else {
        return false;
    };

    super::super::lower_act_body(
        state,
        &body,
        dest_path.clone(),
        &source_scope,
        &act_arg_tvs,
        copy.selected_names.as_ref(),
    );
    state.lower_detail.try_lower_act_copy_from_template += start.elapsed();
    true
}

fn try_copy_lowered_act_body(
    state: &mut LowerState,
    copy: &ActCopy,
    dest_path: &Path,
    dest_args: &[(crate::ids::TypeVar, crate::ids::TypeVar)],
) -> bool {
    let start = Instant::now();
    let source_values = collect_act_copy_source_values(state, copy);
    if source_values.is_empty() {
        state.lower_detail.try_copy_lowered_act_body += start.elapsed();
        return false;
    }
    for (_, def) in &source_values {
        if state.infer.frozen_schemes.borrow().contains_key(def) {
            continue;
        }
        let Some(&tv) = state.def_tvs.get(def) else {
            state.lower_detail.try_copy_lowered_act_body += start.elapsed();
            return false;
        };
        let frozen = freeze_type_var_with_non_generic(
            &state.infer,
            tv,
            &state.infer.non_generic_vars_of(*def),
        );
        state.infer.store_frozen_scheme(*def, frozen);
    }

    let source_effect_args = state
        .effect_args
        .get(&copy.source_path)
        .map(Vec::as_slice)
        .unwrap_or(&[]);
    let subst = source_effect_args
        .iter()
        .zip(copy.source_args.iter())
        .flat_map(|((src_pos, src_neg), (dst_pos, dst_neg))| {
            [(*src_pos, *dst_pos), (*src_neg, *dst_neg)]
        })
        .collect::<Vec<_>>();

    let mut copied_defs = Vec::with_capacity(source_values.len());
    for (name, source_def) in source_values {
        let frozen = {
            let frozen_map = state.infer.frozen_schemes.borrow();
            let Some(source_frozen) = frozen_map.get(&source_def) else {
                return false;
            };
            let source_effect_path = state
                .effect_op_effect_paths
                .get(&source_def)
                .unwrap_or(&copy.source_path);
            super::super::transform_copied_frozen_scheme(
                state,
                source_frozen,
                subst.as_slice(),
                source_effect_path,
                dest_path,
                dest_args,
            )
        };
        let def = state.fresh_def();
        let tv = state.fresh_tv();
        state.register_def_tv(def, tv);
        state.register_def_name(def, name.clone());
        state.insert_value(state.ctx.current_module, name, def);
        instantiate_frozen_scheme(&state.infer, &frozen, tv);
        state.infer.store_frozen_scheme(def, frozen);
        copied_defs.push((source_def, def, tv));
    }

    let copied_def_subst = copied_defs
        .iter()
        .map(|(source_def, def, _)| (*source_def, *def))
        .collect::<HashMap<_, _>>();

    for (source_def, def, tv) in copied_defs {
        if let Some(source_body) = state.principal_bodies.get(&source_def).cloned() {
            let body = super::super::transform_copied_principal_body(
                state,
                &source_body,
                &copied_def_subst,
                &copy.source_path,
                dest_path,
            );
            state.principal_bodies.insert(def, body);
        }

        if let (Some(source_pos_sig), Some(source_neg_sig)) = (
            state.effect_op_pos_sigs.get(&source_def),
            state.effect_op_neg_sigs.get(&source_def),
        ) {
            let source_effect_path = state
                .effect_op_effect_paths
                .get(&source_def)
                .unwrap_or(&copy.source_path);
            let pos_sig = super::super::replace_effect_path_pos(
                &state.infer,
                subst_pos_id(&state.infer, *source_pos_sig, subst.as_slice()),
                source_effect_path,
                dest_path,
                dest_args,
            );
            let neg_sig = super::super::replace_effect_path_neg(
                &state.infer,
                subst_neg_id(&state.infer, *source_neg_sig, subst.as_slice()),
                source_effect_path,
                dest_path,
                dest_args,
            );
            state.effect_op_args.insert(def, dest_args.to_vec());
            state.effect_op_effect_paths.insert(def, dest_path.clone());
            state.effect_op_pos_sigs.insert(def, pos_sig.clone());
            state.effect_op_neg_sigs.insert(def, neg_sig.clone());
            state.infer.constrain(pos_sig, Neg::Var(tv));
            state.infer.constrain(Pos::Var(tv), neg_sig);
        }
    }
    state.lower_detail.try_copy_lowered_act_body += start.elapsed();
    true
}

fn copy_effect_ops_from_source_module(
    state: &mut LowerState,
    copy: &ActCopy,
    dest_path: &Path,
    dest_args: &[(crate::ids::TypeVar, crate::ids::TypeVar)],
) {
    let start = Instant::now();
    let source_effect_args = state
        .effect_args
        .get(&copy.source_path)
        .map(Vec::as_slice)
        .unwrap_or(&[]);
    let subst = source_effect_args
        .iter()
        .zip(copy.source_args.iter())
        .flat_map(|((src_pos, src_neg), (dst_pos, dst_neg))| {
            [(*src_pos, *dst_pos), (*src_neg, *dst_neg)]
        })
        .collect::<Vec<_>>();
    let source_values = collect_act_copy_source_values(state, copy);
    let mut copied_sigs = Vec::with_capacity(source_values.len());

    for (name, source_def) in source_values {
        let Some(source_pos_sig) = state.effect_op_pos_sigs.get(&source_def) else {
            continue;
        };
        let Some(source_neg_sig) = state.effect_op_neg_sigs.get(&source_def) else {
            continue;
        };
        let source_frozen = state
            .infer
            .frozen_schemes
            .borrow()
            .get(&source_def)
            .cloned();
        let source_effect_path = state
            .effect_op_effect_paths
            .get(&source_def)
            .unwrap_or(&copy.source_path)
            .clone();

        copied_sigs.push((
            name,
            super::super::replace_effect_path_pos(
                &state.infer,
                subst_pos_id(&state.infer, *source_pos_sig, subst.as_slice()),
                &source_effect_path,
                dest_path,
                dest_args,
            ),
            super::super::replace_effect_path_neg(
                &state.infer,
                subst_neg_id(&state.infer, *source_neg_sig, subst.as_slice()),
                &source_effect_path,
                dest_path,
                dest_args,
            ),
            source_frozen.as_ref().map(|source| {
                super::super::transform_copied_frozen_scheme(
                    state,
                    source,
                    subst.as_slice(),
                    &source_effect_path,
                    dest_path,
                    dest_args,
                )
            }),
        ));
    }

    for (name, pos_sig, neg_sig, frozen) in copied_sigs {
        let def = state.fresh_def();
        let tv = state.fresh_tv();
        state.register_def_tv(def, tv);
        state.effect_op_args.insert(def, dest_args.to_vec());
        state.effect_op_effect_paths.insert(def, dest_path.clone());
        state.effect_op_pos_sigs.insert(def, pos_sig.clone());
        state.effect_op_neg_sigs.insert(def, neg_sig.clone());
        state.insert_value(state.ctx.current_module, name, def);
        state.infer.constrain(pos_sig, Neg::Var(tv));
        state.infer.constrain(Pos::Var(tv), neg_sig);
        let frozen = frozen.unwrap_or_else(|| {
            crate::scheme::freeze_pos_scheme(&state.infer, state.effect_op_pos_sigs[&def])
        });
        state.infer.store_frozen_scheme(def, frozen);
    }
    state.lower_detail.copy_effect_ops_from_source_module += start.elapsed();
}

fn collect_act_copy_source_values(state: &LowerState, copy: &ActCopy) -> Vec<(Name, DefId)> {
    let module_values = &state.ctx.modules.node(copy.source_module).values;
    let mut source_values = if let Some(selected_names) = copy.selected_names.as_ref() {
        selected_names
            .iter()
            .filter_map(|name| {
                module_values
                    .get(name)
                    .copied()
                    .map(|def| (name.clone(), def))
            })
            .collect::<Vec<_>>()
    } else {
        module_values
            .iter()
            .map(|(name, def)| (name.clone(), *def))
            .collect::<Vec<_>>()
    };
    source_values.sort_by(|lhs, rhs| lhs.0.0.cmp(&rhs.0.0));
    source_values
}
