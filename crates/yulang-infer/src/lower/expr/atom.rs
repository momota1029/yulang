use crate::profile::ProfileClock as Instant;

use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::{ExprKind, Lit, TypedExpr};
use crate::lower::stmt;
use crate::lower::{LowerState, SyntaxNode};

use super::{
    lower_case, lower_catch, lower_expr, lower_if, lower_lambda, lower_list_expr,
    lower_number_token, lower_record_literal, lower_string_lit, lower_tuple_expr, make_app,
    prefix_op_ref, unit_expr,
};

// ── atom lowering ─────────────────────────────────────────────────────────────

/// Expr 以外の葉ノード・特殊ノードを lower する。
///
/// 制約を自分で張るノード（LambdaExpr / CatchExpr 等）は early-return して
/// その TypedExpr の tv/eff をそのまま使う。
pub(super) fn lower_expr_atom(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let start = Instant::now();
    let result = (|| {
        match node.kind() {
            SyntaxKind::LambdaExpr => {
                let atom_start = Instant::now();
                let lowered = lower_lambda(state, node);
                state.lower_detail.lower_expr_atom_lambda += atom_start.elapsed();
                return lowered;
            }
            SyntaxKind::CatchExpr => {
                let atom_start = Instant::now();
                let lowered = lower_catch(state, node);
                state.lower_detail.lower_expr_atom_catch += atom_start.elapsed();
                return lowered;
            }
            SyntaxKind::CaseExpr => {
                let atom_start = Instant::now();
                let lowered = lower_case(state, node);
                state.lower_detail.lower_expr_atom_case += atom_start.elapsed();
                return lowered;
            }
            SyntaxKind::IfExpr => {
                let atom_start = Instant::now();
                let lowered = lower_if(state, node);
                state.lower_detail.lower_expr_atom_if += atom_start.elapsed();
                return lowered;
            }
            SyntaxKind::PrefixNode => {
                let atom_start = Instant::now();
                let operand = node
                    .children()
                    .find(|c| c.kind() == SyntaxKind::Expr)
                    .map(|expr| lower_expr(state, &expr))
                    .unwrap_or_else(|| unit_expr(state));
                let op_ref = prefix_op_ref(state, node);
                let lowered = make_app(state, op_ref, operand);
                state.lower_detail.lower_expr_atom_literal += atom_start.elapsed();
                return lowered;
            }
            SyntaxKind::Number => {
                let atom_start = Instant::now();
                let lowered =
                    lower_number_token(state, &node.text().to_string(), Some(node.text_range()));
                state.lower_detail.lower_expr_atom_literal += atom_start.elapsed();
                return lowered;
            }
            SyntaxKind::StringLit => {
                let atom_start = Instant::now();
                let lowered = lower_string_lit(state, node);
                state.lower_detail.lower_expr_atom_literal += atom_start.elapsed();
                return lowered;
            }
            SyntaxKind::Paren => {
                let items = node
                    .children()
                    .filter(|c| c.kind() == SyntaxKind::Expr)
                    .collect::<Vec<_>>();
                if items.is_empty() {
                    return unit_expr(state);
                }
                if items.len() == 1 {
                    return lower_expr(state, &items[0]);
                }
                if !items.is_empty() {
                    let atom_start = Instant::now();
                    let lowered = lower_tuple_expr(state, items);
                    state.lower_detail.lower_expr_atom_tuple += atom_start.elapsed();
                    return lowered;
                }
            }
            SyntaxKind::Bracket => {
                let items = node
                    .children()
                    .filter(|c| matches!(c.kind(), SyntaxKind::Expr | SyntaxKind::ExprSpread))
                    .collect::<Vec<_>>();
                let atom_start = Instant::now();
                let lowered = lower_list_expr(state, items);
                state.lower_detail.lower_expr_atom_literal += atom_start.elapsed();
                return lowered;
            }
            _ => {}
        }

        let tv = state.fresh_tv();
        let eff = state.fresh_exact_pure_eff_tv();

        let kind = match node.kind() {
            SyntaxKind::Bracket => {
                let atom_start = Instant::now();
                state.lower_detail.lower_expr_atom_literal += atom_start.elapsed();
                ExprKind::Lit(Lit::Unit)
            }
            SyntaxKind::BraceGroup | SyntaxKind::IndentBlock => {
                let atom_start = Instant::now();
                if node.kind() == SyntaxKind::BraceGroup {
                    if let Some(record) = lower_record_literal(state, node) {
                        state.lower_detail.lower_expr_atom_record += atom_start.elapsed();
                        return record;
                    }
                }
                let saved_do = state.do_replacement.take();
                let block = stmt::lower_block(state, node);
                state.do_replacement = saved_do;
                state.lower_detail.lower_expr_atom_block += atom_start.elapsed();
                return TypedExpr {
                    tv: block.tv,
                    eff: block.eff,
                    kind: ExprKind::Block(block),
                };
            }
            _ => {
                let atom_start = Instant::now();
                state.lower_detail.lower_expr_atom_literal += atom_start.elapsed();
                ExprKind::Lit(Lit::Unit)
            }
        };
        TypedExpr { tv, eff, kind }
    })();
    state.lower_detail.lower_expr_atom += start.elapsed();
    result
}
