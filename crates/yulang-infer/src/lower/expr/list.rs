use crate::ast::expr::{ExprKind, TypedExpr};
use crate::ids::TypeVar;
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::{Name, Path};
use crate::types::{Neg, Pos};
use yulang_parser::lex::SyntaxKind;

use super::{lower_expr, make_app, unit_expr};

pub(super) fn lower_list_expr(state: &mut LowerState, items: Vec<SyntaxNode>) -> TypedExpr {
    let item_tv = state.fresh_tv();
    let parts = items
        .into_iter()
        .map(|item| lower_list_item_expr(state, &item))
        .collect::<Vec<_>>();
    build_list_expr(state, item_tv, &parts)
}

#[derive(Debug, Clone)]
enum ListItemExpr {
    Single(TypedExpr),
    Spread(TypedExpr),
}

fn lower_list_item_expr(state: &mut LowerState, item: &SyntaxNode) -> ListItemExpr {
    if item.kind() == SyntaxKind::ExprSpread {
        let expr = item
            .children()
            .find(|child| child.kind() == SyntaxKind::Expr)
            .map(|child| lower_expr(state, &child))
            .unwrap_or_else(|| unit_expr(state));
        ListItemExpr::Spread(expr)
    } else {
        ListItemExpr::Single(lower_expr(state, item))
    }
}

fn build_list_expr(state: &mut LowerState, item_tv: TypeVar, items: &[ListItemExpr]) -> TypedExpr {
    if items.is_empty() {
        let empty = specialized_list_empty_expr(state, item_tv);
        let unit = unit_expr(state);
        return make_app(state, empty, unit);
    }
    if items.len() == 1 {
        return lower_list_part_expr(state, item_tv, &items[0]);
    }
    let mid = items.len() / 2;
    let left = build_list_expr(state, item_tv, &items[..mid]);
    let right = build_list_expr(state, item_tv, &items[mid..]);
    let merge = specialized_list_merge_expr(state, item_tv);
    let app = make_app(state, merge, left);
    make_app(state, app, right)
}

fn lower_list_part_expr(
    state: &mut LowerState,
    item_tv: TypeVar,
    item: &ListItemExpr,
) -> TypedExpr {
    match item {
        ListItemExpr::Single(expr) => {
            let singleton = specialized_list_singleton_expr(state, item_tv);
            make_app(state, singleton, expr.clone())
        }
        ListItemExpr::Spread(expr) => {
            constrain_list_expr(state, item_tv, expr);
            expr.clone()
        }
    }
}

fn constrain_list_expr(state: &mut LowerState, item_tv: TypeVar, expr: &TypedExpr) {
    let list_path = builtin_list_path();
    let list_args = vec![(Pos::Var(item_tv), Neg::Var(item_tv))];
    state.infer.constrain(
        state.pos_con(list_path.clone(), list_args.clone()),
        Neg::Var(expr.tv),
    );
    state
        .infer
        .constrain(Pos::Var(expr.tv), state.neg_con(list_path, list_args));
}

fn specialized_list_empty_expr(state: &mut LowerState, item_tv: TypeVar) -> TypedExpr {
    let tv = state.fresh_tv();
    let eff = state.fresh_exact_pure_eff_tv();
    let unit_path = Path {
        segments: vec![Name("unit".to_string())],
    };
    let list_path = builtin_list_path();
    let list_args = vec![(Pos::Var(item_tv), Neg::Var(item_tv))];
    let pos_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_ret_eff = state.fresh_exact_pure_eff_tv();
    state.infer.constrain(
        state.pos_fun(
            state.neg_con(unit_path.clone(), vec![]),
            Neg::Var(pos_arg_eff),
            Pos::Var(pos_ret_eff),
            state.pos_con(list_path.clone(), list_args.clone()),
        ),
        Neg::Var(tv),
    );
    state.infer.constrain(
        Pos::Var(tv),
        state.neg_fun(
            state.pos_con(unit_path, vec![]),
            Pos::Var(neg_arg_eff),
            Neg::Var(neg_ret_eff),
            state.neg_con(list_path, list_args),
        ),
    );
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::PrimitiveOp(yulang_core_ir::PrimitiveOp::ListEmpty),
    }
}

fn specialized_list_singleton_expr(state: &mut LowerState, item_tv: TypeVar) -> TypedExpr {
    let tv = state.fresh_tv();
    let eff = state.fresh_exact_pure_eff_tv();
    let list_path = builtin_list_path();
    let list_args = vec![(Pos::Var(item_tv), Neg::Var(item_tv))];
    let pos_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_ret_eff = state.fresh_exact_pure_eff_tv();
    state.infer.constrain(
        state.pos_fun(
            Neg::Var(item_tv),
            Neg::Var(pos_arg_eff),
            Pos::Var(pos_ret_eff),
            state.pos_con(list_path.clone(), list_args.clone()),
        ),
        Neg::Var(tv),
    );
    state.infer.constrain(
        Pos::Var(tv),
        state.neg_fun(
            Pos::Var(item_tv),
            Pos::Var(neg_arg_eff),
            Neg::Var(neg_ret_eff),
            state.neg_con(list_path, list_args),
        ),
    );
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::PrimitiveOp(yulang_core_ir::PrimitiveOp::ListSingleton),
    }
}

fn specialized_list_merge_expr(state: &mut LowerState, item_tv: TypeVar) -> TypedExpr {
    let tv = state.fresh_tv();
    let eff = state.fresh_exact_pure_eff_tv();
    let list_path = builtin_list_path();
    let list_args = vec![(Pos::Var(item_tv), Neg::Var(item_tv))];
    let pos_outer_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_outer_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_inner_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_inner_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_outer_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_outer_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_inner_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_inner_ret_eff = state.fresh_exact_pure_eff_tv();
    state.infer.constrain(
        state.pos_fun(
            state.neg_con(list_path.clone(), list_args.clone()),
            Neg::Var(pos_outer_arg_eff),
            Pos::Var(pos_outer_ret_eff),
            state.pos_fun(
                state.neg_con(list_path.clone(), list_args.clone()),
                Neg::Var(pos_inner_arg_eff),
                Pos::Var(pos_inner_ret_eff),
                state.pos_con(list_path.clone(), list_args.clone()),
            ),
        ),
        Neg::Var(tv),
    );
    state.infer.constrain(
        Pos::Var(tv),
        state.neg_fun(
            state.pos_con(list_path.clone(), list_args.clone()),
            Pos::Var(neg_outer_arg_eff),
            Neg::Var(neg_outer_ret_eff),
            state.neg_fun(
                state.pos_con(list_path.clone(), list_args.clone()),
                Pos::Var(neg_inner_arg_eff),
                Neg::Var(neg_inner_ret_eff),
                state.neg_con(list_path, list_args),
            ),
        ),
    );
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::PrimitiveOp(yulang_core_ir::PrimitiveOp::ListMerge),
    }
}

fn builtin_list_path() -> Path {
    Path {
        segments: vec![
            Name("std".to_string()),
            Name("list".to_string()),
            Name("list".to_string()),
        ],
    }
}
