use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::{PatKind, TypedPat};
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::Name;

/// BindingHeader の Pattern から「束縛パターン」と「引数パターンリスト」を取り出す。
///
/// - `my x = e`    -> (UnresolvedName("x"), [])
/// - `my f x = e`  -> (UnresolvedName("f"), [(def_x, tv_x)])
/// - `my (a,b)= e` -> (Tuple([...]), [])
pub(crate) fn extract_binding_lhs(
    node: &SyntaxNode,
    state: &mut LowerState,
    header: &SyntaxNode,
) -> Option<(TypedPat, Vec<super::super::ArgPatInfo>)> {
    if node.kind() == SyntaxKind::OpDef {
        let name = super::super::header_value_name(header)?;
        let fixity = super::super::header_operator_fixity(header)?;
        let bind_pat = TypedPat {
            tv: state.fresh_tv(),
            kind: PatKind::As(
                Box::new(TypedPat {
                    tv: state.fresh_tv(),
                    kind: PatKind::Wild,
                }),
                state.ctx.resolve_operator_value(&name, fixity)?,
            ),
        };
        return Some((bind_pat, vec![]));
    }

    let pat_node = super::super::child_node(header, SyntaxKind::Pattern)?;
    let direct_ident = direct_binding_name(&pat_node);

    if let Some(name) = direct_ident {
        let arg_pats = super::super::collect_header_args(&pat_node)
            .into_iter()
            .map(|header_arg| super::super::make_arg_pat_info(state, header_arg))
            .collect();
        let bind_pat = TypedPat {
            tv: state.fresh_tv(),
            kind: PatKind::UnresolvedName(name),
        };
        return Some((bind_pat, arg_pats));
    }

    let bind_pat = super::super::lower_pat(state, &pat_node);
    Some((bind_pat, vec![]))
}

pub(crate) fn direct_binding_name(pat_node: &SyntaxNode) -> Option<Name> {
    pat_node
        .children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| t.kind() == SyntaxKind::Ident)
        .map(|t| Name(t.text().to_string()))
}
