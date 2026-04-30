//! 式の lowering。
//!
//! ## Expr ノードの構造
//!
//! パーサは式を「ヘッド + サフィックスの chain」として表現する。
//!
//! ```text
//! Expr
//!   Ident "foo"          ← ヘッド（token）
//!   PathSep              ← サフィックス: ::bar
//!     ColonColon "::"
//!     Ident "bar"
//!   ApplyC               ← サフィックス: (x)
//!     ParenL "("
//!     Expr ...
//!     ParenR ")"
//! ```
//!
//! lowering では:
//! 1. ヘッドと先頭の PathSep* を集めてパスを構築
//! 2. パスを名前解決して TypedExpr を作る
//! 3. 残りのサフィックス（Field / Apply* / InfixNode / PipeNode 等）を左結合で畳む
//!
//! `x.foo::bar` は通常の field selection ではなく `foo::bar x` として
//! lower する。修飾済み関数を method 風に書くための局所 sugar。

use crate::profile::ProfileClock as Instant;

use yulang_parser::lex::SyntaxKind;

use super::stmt::connect_pat_shape_and_locals;
use super::{LowerState, SyntaxNode};
use crate::ast::expr::{ExprKind, Lit, TypedExpr};
use crate::diagnostic::TypeOrigin;
use crate::types::Neg;

mod apply;
mod arms;
mod atom;
mod bool_ops;
mod catch;
mod chain;
mod control;
mod effect_rows;
mod lambda;
mod list;
mod literal;
mod operator;
mod path;
mod prim;
mod record;
mod suffix;
mod tuple;
mod var;

pub(super) use apply::{make_app, make_app_with_cause};
pub(super) use arms::collect_child_arms;
use atom::lower_expr_atom;
use bool_ops::{lower_not_equal_infix, lower_short_circuit_infix};
use catch::{debug_dump_effect_tv, lower_catch};
use chain::lower_expr_chain;
use control::{lower_case, lower_if};
pub(super) use effect_rows::{neg_id_is_pure_row, pos_id_is_empty_row};
use lambda::lower_lambda;
use list::lower_list_expr;
use literal::{lower_number_token, lower_string_lit};
use operator::{infix_op_name, infix_op_ref, prefix_op_ref, suffix_op_ref};
pub(super) use path::resolve_path_expr;
use path::{resolve_bound_def_expr, resolve_operator_expr};
use prim::{neg_prim_type, prim_type};
use record::lower_record_literal;
use suffix::{apply_suffix, apply_synthetic_field_selection};
use tuple::lower_tuple_expr;
use var::{lower_var_assignment, lower_var_read_expr};

// ── エントリポイント ──────────────────────────────────────────────────────────

pub fn lower_expr(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let start = Instant::now();
    let result = match node.kind() {
        SyntaxKind::Expr => lower_expr_chain(state, node),
        _ => lower_expr_atom(state, node),
    };
    state.lower_detail.lower_expr += start.elapsed();
    result
}

// ── catch ─────────────────────────────────────────────────────────────────────

// ── ヘルパー ──────────────────────────────────────────────────────────────────

pub(super) fn unit_expr(state: &mut LowerState) -> TypedExpr {
    let tv = state.fresh_tv_with_origin(TypeOrigin::synthetic("unit"));
    let eff = state.fresh_exact_pure_eff_tv();
    state.infer.constrain(prim_type("unit"), Neg::Var(tv));
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::Lit(Lit::Unit),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::Pos;

    #[test]
    fn app_inherits_effect_from_partial_application() {
        let mut state = LowerState::new();
        let func = unit_expr(&mut state);
        let arg1 = unit_expr(&mut state);
        let arg2 = unit_expr(&mut state);

        let app1 = make_app(&mut state, func, arg1);
        let app2 = make_app(&mut state, app1.clone(), arg2);

        assert!(
            state
                .infer
                .lowers_of(app2.eff)
                .contains(&Pos::Var(app1.eff)),
            "outer application should inherit effect from inner partial application",
        );
    }

    #[test]
    fn app_connects_argument_effect_to_function_arg_effect_slot() {
        let mut state = LowerState::new();
        let func = unit_expr(&mut state);
        let arg = unit_expr(&mut state);

        let app = make_app(&mut state, func.clone(), arg.clone());

        let upper_fun = state
            .infer
            .uppers_of(func.tv)
            .into_iter()
            .find_map(|neg| match neg {
                Neg::Fun { arg_eff, .. } => Some(arg_eff),
                _ => None,
            })
            .expect("application should constrain function with Fun upper bound");
        let arg_eff_tv = match state.infer.arena.get_pos(upper_fun) {
            Pos::Var(tv) => tv,
            other => panic!("expected arg_eff slot to be a var, got {other:?}"),
        };

        assert!(
            arg_eff_tv == arg.eff,
            "argument expression effect should be passed to function arg_eff slot directly",
        );
        assert!(
            !state.infer.lowers_of(app.eff).contains(&Pos::Var(arg.eff)),
            "argument expression effect should not flow into total application effect directly",
        );
    }

    #[test]
    fn app_separates_callee_effect_from_total_expression_effect() {
        let mut state = LowerState::new();
        let func = unit_expr(&mut state);
        let arg = unit_expr(&mut state);

        let app = make_app(&mut state, func.clone(), arg.clone());

        let ret_eff = state
            .infer
            .uppers_of(func.tv)
            .into_iter()
            .find_map(|neg| match neg {
                Neg::Fun { ret_eff, .. } => Some(ret_eff),
                _ => None,
            })
            .expect("application should constrain function with Fun upper bound");
        let call_eff_tv = match state.infer.arena.get_neg(ret_eff) {
            Neg::Var(tv) => tv,
            other => panic!("expected ret_eff slot to be a var, got {other:?}"),
        };

        assert_ne!(
            call_eff_tv, app.eff,
            "callee effect should not be the same variable as total application effect",
        );
        assert!(
            state
                .infer
                .lowers_of(app.eff)
                .contains(&Pos::Var(call_eff_tv)),
            "total application effect should include callee effect",
        );
    }
}
