use std::collections::HashMap;

use yulang_parser::lex::SyntaxKind;

use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::{Name, Path};

#[derive(Debug, Clone)]
pub(crate) struct ActCopy {
    pub(crate) source_path: Path,
    pub(crate) source_args: Vec<(crate::ids::TypeVar, crate::ids::TypeVar)>,
    pub(crate) source_module: crate::symbols::ModuleId,
    pub(crate) selected_names: Option<Vec<Name>>,
}

pub(crate) fn prepare_act_copy(
    state: &mut LowerState,
    node: &SyntaxNode,
    act_scope: &HashMap<String, crate::ids::TypeVar>,
    dest_args: &[(crate::ids::TypeVar, crate::ids::TypeVar)],
) -> Option<ActCopy> {
    let source_sig = act_copy_source_sig(node)?;
    let (source_path, source_arg_sigs) = crate::lower::signature::sig_type_head(&source_sig)?;
    let canonical_source_path = state.ctx.canonical_current_type_path(&source_path);
    let source_module = state
        .ctx
        .resolve_module_path(&canonical_source_path)
        .or_else(|| state.ctx.resolve_module_path(&source_path))?;
    let source_effect_args = state.effect_args.get(&canonical_source_path)?.clone();

    let source_args = if source_arg_sigs.is_empty() && source_effect_args.len() == dest_args.len() {
        dest_args.to_vec()
    } else {
        let mut vars = act_scope.clone();
        source_arg_sigs
            .iter()
            .map(|arg| crate::lower::signature::lower_sig_effect_arg(state, arg, &mut vars))
            .collect::<Vec<_>>()
    };

    if source_args.len() != source_effect_args.len() {
        return None;
    }

    Some(ActCopy {
        source_path: canonical_source_path,
        source_args,
        source_module,
        selected_names: None,
    })
}

fn act_copy_source_sig(node: &SyntaxNode) -> Option<crate::lower::signature::SigType> {
    let mut after_equal = false;
    for item in node.children_with_tokens() {
        match item {
            rowan::NodeOrToken::Token(token) if token.kind() == SyntaxKind::Equal => {
                after_equal = true;
            }
            rowan::NodeOrToken::Node(child)
                if after_equal && child.kind() == SyntaxKind::TypeExpr =>
            {
                return crate::lower::signature::parse_sig_type_expr(&child);
            }
            _ => {}
        }
    }
    None
}
