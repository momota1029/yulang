use std::collections::HashMap;

use crate::ids::TypeVar;
use crate::lower::{LowerState, SyntaxNode};

pub(crate) fn collect_act_type_scope(
    state: &mut LowerState,
    node: &SyntaxNode,
) -> HashMap<String, TypeVar> {
    crate::lower::signature::fresh_type_scope(
        state,
        &crate::lower::signature::act_type_param_names(node),
    )
}
