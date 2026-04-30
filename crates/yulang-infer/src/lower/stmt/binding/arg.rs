use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::{PatKind, TypedPat};
use crate::diagnostic::{TypeOrigin, TypeOriginKind};
use crate::ids::DefId;
use crate::lower::ann::{LoweredEffAnn, LoweredPatAnn, fresh_arg_effect_tv, lower_pat_ann};
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::Name;
use crate::types::Neg;

#[derive(Debug, Clone)]
pub(crate) struct ArgPatInfo {
    pub(crate) def: DefId,
    pub(crate) tv: crate::ids::TypeVar,
    pub(crate) arg_eff_tv: crate::ids::TypeVar,
    pub(crate) read_eff_tv: Option<crate::ids::TypeVar>,
    pub(crate) pat: Option<TypedPat>,
    pub(crate) local_bindings: Vec<(Name, DefId)>,
    pub(crate) ann: Option<LoweredPatAnn>,
    pub(crate) unit_arg: bool,
}

pub(crate) enum HeaderArg {
    Pattern(SyntaxNode),
    Unit,
}

pub(crate) fn collect_header_args(pat_node: &SyntaxNode) -> Vec<HeaderArg> {
    let mut args = Vec::new();
    collect_nested_header_args(pat_node, &mut args);
    args
}

pub(crate) fn make_arg_pat_info(state: &mut LowerState, header_arg: HeaderArg) -> ArgPatInfo {
    match header_arg {
        HeaderArg::Pattern(param_pat) if is_unit_arg_pattern(&param_pat) => {
            let def = state.fresh_def();
            let tv = state.fresh_tv();
            let arg_eff_tv = state.fresh_exact_pure_eff_tv();
            state.register_def_tv(def, tv);
            ArgPatInfo {
                def,
                tv,
                arg_eff_tv,
                read_eff_tv: None,
                pat: None,
                local_bindings: Vec::new(),
                ann: None,
                unit_arg: true,
            }
        }
        HeaderArg::Pattern(param_pat) => {
            let def = state.fresh_def();
            let tv = state.fresh_tv();
            let ann = lower_pat_ann(state, &param_pat);
            let hint = super::super::connect_pattern_sig_annotation(state, &param_pat, tv, None);
            let arg_eff_tv = fresh_arg_effect_tv(state, ann.as_ref());
            let read_eff_tv = ann.as_ref().map(|ann| match ann.eff {
                Some(LoweredEffAnn::Row { .. }) | Some(LoweredEffAnn::Opaque) => state
                    .fresh_tv_with_origin(TypeOrigin {
                        span: Some(ann.span),
                        kind: TypeOriginKind::Annotation,
                        label: Some("argument read effect".to_string()),
                    }),
                None => match hint {
                    Some(crate::lower::FunctionSigEffectHint::Pure) | None => arg_eff_tv,
                    Some(_) => state.fresh_exact_pure_eff_tv(),
                },
            });
            state.register_def_tv(def, tv);
            if let Some(read_eff_tv) = read_eff_tv {
                state.register_def_eff_tv(def, read_eff_tv);
            }
            let (pat, local_bindings) =
                if let Some(name) = header_arg_direct_binding_name(&param_pat) {
                    (
                        Some(TypedPat {
                            tv,
                            kind: PatKind::UnresolvedName(name.clone()),
                        }),
                        vec![(name, def)],
                    )
                } else {
                    state.ctx.push_local();
                    super::super::bind_pattern_locals(state, &param_pat);
                    let pat = super::super::lower_pat(state, &param_pat);
                    let local_bindings = state.ctx.pop_local_frame().into_iter().collect();
                    (Some(pat), local_bindings)
                };
            if let Some(hint) = hint {
                state.register_lambda_param_function_sig(def, hint);
            }
            if let Some(allowed) = exportable_function_sig_allowed_effects(&param_pat) {
                state.register_lambda_param_function_allowed_effects(def, allowed);
            }
            if let Some(annotation) = exportable_param_effect_annotation(&param_pat, ann.as_ref()) {
                state.register_lambda_param_effect_annotation(def, annotation);
            }
            for (name, def) in &local_bindings {
                state.register_def_name(*def, name.clone());
            }
            ArgPatInfo {
                def,
                tv,
                arg_eff_tv,
                read_eff_tv,
                pat,
                local_bindings,
                ann,
                unit_arg: false,
            }
        }
        HeaderArg::Unit => {
            let def = state.fresh_def();
            let tv = state.fresh_tv();
            let arg_eff_tv = state.fresh_exact_pure_eff_tv();
            state.register_def_tv(def, tv);
            ArgPatInfo {
                def,
                tv,
                arg_eff_tv,
                read_eff_tv: None,
                pat: None,
                local_bindings: Vec::new(),
                ann: None,
                unit_arg: true,
            }
        }
    }
}

pub(crate) fn configure_read_effect_from_ann(
    state: &mut LowerState,
    read_eff_tv: crate::ids::TypeVar,
    ann: &LoweredPatAnn,
) {
    match ann.eff.clone() {
        Some(LoweredEffAnn::Opaque) => {
            state.infer.mark_through(read_eff_tv);
        }
        Some(LoweredEffAnn::Row { lower, .. }) => {
            state.infer.constrain(lower, Neg::Var(read_eff_tv));
        }
        _ => {}
    }
}

fn header_arg_direct_binding_name(param_pat: &SyntaxNode) -> Option<Name> {
    if param_pat.children().any(|child| {
        matches!(
            child.kind(),
            SyntaxKind::ApplyML
                | SyntaxKind::ApplyC
                | SyntaxKind::PatRecord
                | SyntaxKind::PatParenGroup
                | SyntaxKind::PatOr
                | SyntaxKind::PatAs
                | SyntaxKind::PathSep
        )
    }) {
        return None;
    }
    super::super::pattern_binding_name(param_pat)
}

fn is_unit_arg_pattern(node: &SyntaxNode) -> bool {
    match node.kind() {
        SyntaxKind::Pattern => node
            .children()
            .find(|child| {
                matches!(
                    child.kind(),
                    SyntaxKind::Pattern
                        | SyntaxKind::PatOr
                        | SyntaxKind::PatAs
                        | SyntaxKind::PatParenGroup
                        | SyntaxKind::ApplyC
                )
            })
            .map(|child| is_unit_arg_pattern(&child))
            .unwrap_or(false),
        SyntaxKind::PatParenGroup | SyntaxKind::ApplyC => !node.children().any(|child| {
            matches!(
                child.kind(),
                SyntaxKind::Pattern
                    | SyntaxKind::PatOr
                    | SyntaxKind::PatAs
                    | SyntaxKind::PatParenGroup
            )
        }),
        _ => false,
    }
}

fn collect_nested_header_args(node: &SyntaxNode, out: &mut Vec<HeaderArg>) {
    for child in node.children() {
        if !matches!(child.kind(), SyntaxKind::ApplyML | SyntaxKind::ApplyC) {
            continue;
        }
        collect_nested_header_args(&child, out);
        let mut saw_pattern = false;
        for pat in child.children().filter(|c| c.kind() == SyntaxKind::Pattern) {
            saw_pattern = true;
            out.push(HeaderArg::Pattern(pat));
        }
        if !saw_pattern && child.kind() == SyntaxKind::ApplyC {
            out.push(HeaderArg::Unit);
        }
    }
}

fn exportable_param_effect_annotation(
    pat: &SyntaxNode,
    ann: Option<&LoweredPatAnn>,
) -> Option<yulang_core_ir::ParamEffectAnnotation> {
    match ann.and_then(|ann| ann.eff.as_ref()) {
        Some(LoweredEffAnn::Opaque) => Some(yulang_core_ir::ParamEffectAnnotation::Wildcard),
        Some(LoweredEffAnn::Row { .. }) => first_effect_annotation_region(pat).map(|name| {
            yulang_core_ir::ParamEffectAnnotation::Region(yulang_core_ir::Name(name.0))
        }),
        None => None,
    }
}

fn exportable_function_sig_allowed_effects(
    pat: &SyntaxNode,
) -> Option<yulang_core_ir::FunctionSigAllowedEffects> {
    let type_expr = super::super::child_node(pat, SyntaxKind::TypeAnn)
        .and_then(|ann| super::super::child_node(&ann, SyntaxKind::TypeExpr))?;
    let sig = crate::lower::signature::parse_sig_type_expr(&type_expr)?;
    let crate::lower::signature::SigType::Fun { ret_eff, .. } = sig else {
        return None;
    };
    let row = ret_eff?;
    if row.items.is_empty() {
        return row
            .tail
            .is_some()
            .then_some(yulang_core_ir::FunctionSigAllowedEffects::Wildcard)
            .or(Some(yulang_core_ir::FunctionSigAllowedEffects::Effects(
                Vec::new(),
            )));
    }
    let mut effects = Vec::new();
    for item in row.items {
        let path = match item {
            crate::lower::signature::SigType::Prim { path, .. }
            | crate::lower::signature::SigType::Apply { path, .. } => path,
            _ => return None,
        };
        effects.push(yulang_core_ir::Path {
            segments: path
                .segments
                .into_iter()
                .map(|segment| yulang_core_ir::Name(segment.0))
                .collect(),
        });
    }
    Some(yulang_core_ir::FunctionSigAllowedEffects::Effects(effects))
}

fn first_effect_annotation_region(pat: &SyntaxNode) -> Option<Name> {
    let ann = super::super::child_node(pat, SyntaxKind::TypeAnn)?;
    let type_expr = super::super::child_node(&ann, SyntaxKind::TypeExpr)?;
    let row = super::super::child_node(&type_expr, SyntaxKind::TypeRow)?;
    row.children()
        .filter(|child| child.kind() == SyntaxKind::TypeExpr)
        .find_map(|child| {
            child
                .children_with_tokens()
                .filter_map(|it| it.into_token())
                .find(|tok| tok.kind() == SyntaxKind::Ident)
                .map(|tok| Name(tok.text().to_string()))
        })
}
