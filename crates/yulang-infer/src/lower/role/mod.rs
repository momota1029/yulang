use std::collections::{HashMap, HashSet};

use yulang_core_ir as core_ir;
use yulang_parser::lex::SyntaxKind;

use super::signature::{
    SigRecordField, SigRow, SigType, SigVar, act_type_param_names, fresh_type_scope,
    lower_pure_sig_neg_id, lower_pure_sig_pos_id, parse_sig_type_expr, render_concrete_sig_type,
    sig_type_head,
};
use super::stmt::{
    ArgPatInfo, binding_sig_var_names, child_node, collect_block_items, collect_header_args,
    has_token, header_value_name, ident_name, lower_binding_body, lower_binding_with_type_scope,
    make_arg_pat_info, preregister_binding, wrap_header_lambdas,
};
use super::where_clause::lower_where_clause;
use super::{LowerState, SyntaxNode};
use crate::ast::expr::TypedPat;
use crate::diagnostic::{ConstraintReason, TypeErrorKind};
use crate::ids::TypeVar;
use crate::scheme::freeze_pos_scheme_with_non_generic;
use crate::simplify::compact::{CompactBounds, compact_neg_expr, compact_pos_expr};
use crate::simplify::cooccur::CompactRoleConstraint;
use crate::solve::{
    RoleArgInfo, RoleConstraint, RoleConstraintArg, RoleImplCandidate, RoleMethodInfo,
};
use crate::symbols::{Name, Path};

mod decl;
mod impls;
mod runtime;
mod subst;

pub(super) use decl::lower_role_decl;
pub(super) use impls::lower_impl_decl;
pub(super) use runtime::{export_runtime_path, export_runtime_sig_row, export_runtime_sig_type};

use runtime::{runtime_export_role_method_scheme, runtime_export_scheme};
use subst::substitute_role_sig_type;
fn collect_role_assoc_type_names(node: &SyntaxNode) -> Vec<String> {
    let mut out = Vec::new();
    collect_role_assoc_type_names_inner(node, &mut out);
    out
}

fn collect_role_assoc_type_names_inner(node: &SyntaxNode, out: &mut Vec<String>) {
    for child in node.children() {
        match child.kind() {
            SyntaxKind::IndentBlock | SyntaxKind::BraceGroup => {
                collect_role_assoc_type_names_inner(&child, out);
            }
            SyntaxKind::TypeDecl => {
                if let Some(name) = ident_name(&child).map(|name| name.0) {
                    if !out.contains(&name) {
                        out.push(name);
                    }
                }
            }
            _ => {}
        }
    }
}

fn collect_impl_assoc_type_equations(node: &SyntaxNode) -> HashMap<String, SigType> {
    let mut out = HashMap::new();
    collect_impl_assoc_type_equations_inner(node, &mut out);
    out
}

fn collect_impl_assoc_type_equations_inner(node: &SyntaxNode, out: &mut HashMap<String, SigType>) {
    for child in node.children() {
        match child.kind() {
            SyntaxKind::IndentBlock | SyntaxKind::BraceGroup => {
                collect_impl_assoc_type_equations_inner(&child, out);
            }
            SyntaxKind::TypeDecl => {
                let Some(name) = ident_name(&child).map(|name| name.0) else {
                    continue;
                };
                let Some(type_expr) = child_node(&child, SyntaxKind::TypeExpr).or_else(|| {
                    child_node(&child, SyntaxKind::IndentBlock)
                        .and_then(|block| child_node(&block, SyntaxKind::TypeExpr))
                }) else {
                    continue;
                };
                let Some(sig) = parse_sig_type_expr(&type_expr) else {
                    continue;
                };
                out.insert(name, sig);
            }
            _ => {}
        }
    }
}
fn compact_role_constraints(
    infer: &crate::solve::Infer,
    def: crate::ids::DefId,
) -> Vec<CompactRoleConstraint> {
    infer
        .role_constraints_of(def)
        .into_iter()
        .map(|constraint| CompactRoleConstraint {
            role: constraint.role,
            args: constraint
                .args
                .into_iter()
                .map(|arg| CompactBounds {
                    self_var: None,
                    lower: compact_pos_expr(infer, arg.pos),
                    upper: compact_neg_expr(infer, arg.neg),
                })
                .collect(),
        })
        .collect()
}

fn path_string(path: &Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

fn canonical_role_path(state: &LowerState, path: &Path) -> Path {
    state.ctx.canonical_current_type_path(path)
}

fn compact_impl_arg_pattern(
    state: &mut LowerState,
    sig: &SigType,
    scope: &HashMap<String, TypeVar>,
) -> crate::simplify::compact::CompactType {
    let mut vars = scope.clone();
    super::signature::compact_sig_pattern_type(state, sig, &mut vars)
}

fn render_impl_arg_pattern(
    state: &mut LowerState,
    sig: &SigType,
    scope: &HashMap<String, TypeVar>,
) -> String {
    render_concrete_sig_type(sig).unwrap_or_else(|| {
        crate::display::dump::format_compact_role_constraint_arg(&CompactBounds {
            self_var: None,
            lower: compact_impl_arg_pattern(state, sig, scope),
            upper: crate::simplify::compact::CompactType::default(),
        })
    })
}

fn collect_fun_input_sig_vars_inner(sig: &SigType, out: &mut HashSet<String>) {
    match sig {
        SigType::Fun { arg, ret, .. } => {
            super::signature::collect_all_sig_vars(arg, out);
            collect_fun_input_sig_vars_inner(ret, out);
        }
        _ => {}
    }
}
