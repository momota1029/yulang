//! Direct expression ownership and Item handoff for the parser.

pub(super) mod case_like;
pub(super) mod delimited;
pub(super) mod for_decl;
pub(super) mod if_expr;
pub(super) mod tails;

mod operator_chain;
mod required_operand;

pub(super) use operator_chain::{
    chain_continuation, continue_normalized_tail, expr_from_nud_normalized, is_led_operator,
    is_nud_item, scan_tail_after_accept_normalized, tail_normalized,
};
#[cfg(test)]
pub(super) use operator_chain::{expr, expr_normalized};
pub(super) use required_operand::{
    emit_required_expression_missing, is_required_operand_boundary, required_expr_item_normalized,
};
