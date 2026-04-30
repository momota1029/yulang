mod block;
mod do_lower;
mod for_stmt;

pub use block::lower_block;
pub(crate) use block::{
    collect_block_items, lower_block_from_items, lower_scoped_with_block_expr_with_tail,
};
pub(crate) use do_lower::{
    binding_is_do_binding, lower_block_expr_from_items, lower_do_binding, lower_do_expr,
    lower_expr_with_synthetic_owner_if_top_level, node_has_do_here, preregister_items_until_do,
};
pub(crate) use for_stmt::lower_for_stmt;
