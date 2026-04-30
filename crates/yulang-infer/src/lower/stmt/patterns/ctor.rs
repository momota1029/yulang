use yulang_parser::lex::SyntaxKind;

use crate::ids::{DefId, RefId};
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::{Name, Path};
use crate::types::{Neg, Pos};

pub(crate) fn pattern_ctor_path(node: &SyntaxNode) -> Option<Path> {
    let mut segments = Vec::new();
    for item in node.children_with_tokens() {
        match item {
            rowan::NodeOrToken::Token(token)
                if matches!(token.kind(), SyntaxKind::Ident | SyntaxKind::SigilIdent) =>
            {
                if segments.is_empty() {
                    segments.push(Name(token.text().to_string()));
                }
            }
            rowan::NodeOrToken::Node(child) if child.kind() == SyntaxKind::PathSep => {
                if let Some(segment) = child
                    .children_with_tokens()
                    .filter_map(|it| it.into_token())
                    .find(|token| token.kind() == SyntaxKind::Ident)
                    .map(|token| Name(token.text().to_string()))
                {
                    segments.push(segment);
                }
            }
            _ => {}
        }
    }
    (!segments.is_empty()).then_some(Path { segments })
}

pub(crate) fn enum_variant_def_for_pattern(state: &LowerState, path: &Path) -> Option<DefId> {
    if path.segments.len() == 1 {
        state.ctx.resolve_value(&path.segments[0])
    } else {
        state.ctx.resolve_path_value(path)
    }
}

pub(crate) fn resolve_pattern_constructor_ref(state: &mut LowerState, def: DefId) -> RefId {
    let tv = state.fresh_tv();

    if let (Some(owner), Some(def_owner)) = (state.current_owner, state.def_owner(def)) {
        if owner != def_owner {
            if let Some(&def_tv) = state.def_tvs.get(&def) {
                state.infer.add_non_generic_var(owner, def_tv);
            }
        }
    }

    if let Some(scheme) = state.infer.frozen_schemes.borrow().get(&def) {
        if state.infer.compact_schemes.borrow().get(&def).is_some()
            || state.current_owner.is_none()
            || !state.is_let_bound_def(def)
        {
            let subst =
                crate::scheme::instantiate_frozen_scheme_with_subst(&state.infer, scheme, tv, &[]);
            if let Some(owner) = state.current_owner {
                state
                    .infer
                    .instantiate_role_constraints_for_owner(def, owner, &subst);
            }
        } else if let Some(owner) = state.current_owner {
            if owner != def {
                state.infer.add_edge(owner, def);
            }
        }
    } else if let Some(&def_tv) = state.def_tvs.get(&def) {
        if state.is_let_bound_def(def) && state.current_owner != Some(def) {
            if let Some(owner) = state.current_owner {
                state.infer.add_edge(owner, def);
            } else {
                state.infer.constrain(Pos::Var(def_tv), Neg::Var(tv));
                state.infer.constrain(Pos::Var(tv), Neg::Var(def_tv));
            }
        } else {
            state.infer.constrain(Pos::Var(def_tv), Neg::Var(tv));
            state.infer.constrain(Pos::Var(tv), Neg::Var(def_tv));
        }
    }

    let ref_id = state.ctx.fresh_ref();
    state.ctx.refs.resolve(ref_id, def, tv, state.current_owner);
    ref_id
}
