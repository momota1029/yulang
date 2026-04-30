use yulang_parser::lex::SyntaxKind;

use crate::ids::DefId;
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::{Name, Path};

#[derive(Debug, Clone)]
pub(crate) struct GlobalExtensionMethodHeader {
    pub(crate) name: Name,
    pub(crate) recv_pat: SyntaxNode,
    pub(crate) full_pat: SyntaxNode,
}

pub(crate) fn global_extension_method_header(
    header: &SyntaxNode,
) -> Option<GlobalExtensionMethodHeader> {
    if header.kind() == SyntaxKind::OpDefHeader {
        return None;
    }
    let pattern = super::super::child_node(header, SyntaxKind::Pattern)?;
    let name = pattern
        .children()
        .find(|c| c.kind() == SyntaxKind::Field)
        .and_then(|field| {
            field
                .children_with_tokens()
                .filter_map(|it| it.into_token())
                .find(|t| t.kind() == SyntaxKind::DotField)
                .map(|t| Name(t.text().trim_start_matches('.').trim().to_string()))
        })?;
    let recv_pat = pattern
        .children()
        .find(|child| child.kind() == SyntaxKind::PatParenGroup)
        .and_then(|group| super::super::child_node(&group, SyntaxKind::Pattern))?;
    Some(GlobalExtensionMethodHeader {
        name,
        recv_pat,
        full_pat: pattern,
    })
}

pub(crate) fn current_module_extension_method_def(
    state: &LowerState,
    name: &Name,
) -> Option<DefId> {
    state
        .infer
        .extension_methods
        .get(name)?
        .iter()
        .rev()
        .find_map(|info| (info.module == state.ctx.current_module).then_some(info.def))
}

pub(crate) fn current_module_effect_method_def(state: &LowerState, name: &Name) -> Option<DefId> {
    state
        .infer
        .effect_methods
        .get(name)?
        .iter()
        .rev()
        .find_map(|info| {
            (info.module == state.ctx.current_module
                && state
                    .current_act_effect_path
                    .as_ref()
                    .is_some_and(|effect| *effect == info.effect))
            .then_some(info.def)
        })
}

pub(crate) fn extension_method_hidden_name(name: &Name, def: DefId) -> Name {
    Name(format!("#ext:{}:{}", name.0, def.0))
}

pub(crate) fn effect_method_hidden_name(effect: &Path, name: &Name, def: DefId) -> Name {
    Name(format!(
        "#effect-method:{}:{}:{}",
        effect
            .segments
            .iter()
            .map(|segment| segment.0.as_str())
            .collect::<Vec<_>>()
            .join("::"),
        name.0,
        def.0
    ))
}
