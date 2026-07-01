//! CST accessors for `if`, `case`, and `catch` forms.

use super::*;

pub(super) fn case_like_scrutinee_expr(node: &Cst) -> Option<Cst> {
    node.children()
        .find(|child| child.kind() == SyntaxKind::Expr)
}

pub(super) fn case_like_label(node: &Cst) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::SigilIdent)
        .map(|token| Name(token.text().to_string()))
}

pub(super) fn case_arm_nodes(node: &Cst) -> Vec<Cst> {
    node.children()
        .filter(|child| child.kind() == SyntaxKind::CaseBlock)
        .flat_map(|block| arm_nodes(&block, SyntaxKind::CaseArm))
        .collect()
}

pub(super) fn catch_arm_nodes(node: &Cst) -> Vec<Cst> {
    node.children()
        .filter(|child| child.kind() == SyntaxKind::CatchBlock)
        .flat_map(|block| arm_nodes(&block, SyntaxKind::CatchArm))
        .collect()
}

pub(super) fn if_arm_nodes(node: &Cst) -> Vec<Cst> {
    node.children()
        .filter(|child| child.kind() == SyntaxKind::IfArm)
        .collect()
}

pub(super) fn else_arm_node(node: &Cst) -> Option<Cst> {
    node.children()
        .find(|child| child.kind() == SyntaxKind::ElseArm)
}

pub(super) fn if_arm_condition_expr(arm: &Cst) -> Option<Cst> {
    arm.children()
        .find(|child| child.kind() == SyntaxKind::Cond)?
        .children()
        .find(|child| child.kind() == SyntaxKind::Expr)
}

pub(super) fn if_arm_body_expr(arm: &Cst) -> Option<Cst> {
    arm.children().find(|child| {
        matches!(
            child.kind(),
            SyntaxKind::Expr | SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
        )
    })
}

fn arm_nodes(block: &Cst, kind: SyntaxKind) -> Vec<Cst> {
    block
        .children()
        .filter(|child| child.kind() == kind)
        .collect()
}

pub(super) fn arm_pattern(arm: &Cst) -> Option<Cst> {
    arm_patterns(arm).into_iter().next()
}

pub(super) fn arm_guard_expr(arm: &Cst) -> Option<Cst> {
    arm.children()
        .find(|child| matches!(child.kind(), SyntaxKind::CaseGuard | SyntaxKind::CatchGuard))?
        .children()
        .find(|child| child.kind() == SyntaxKind::Expr)
}

pub(super) fn arm_patterns(arm: &Cst) -> Vec<Cst> {
    arm.children()
        .filter(|child| {
            matches!(
                child.kind(),
                SyntaxKind::Pattern
                    | SyntaxKind::PatOr
                    | SyntaxKind::PatAs
                    | SyntaxKind::PatParenGroup
                    | SyntaxKind::PatList
            )
        })
        .collect()
}

pub(super) fn arm_body_expr(arm: &Cst) -> Option<Cst> {
    arm.children()
        .filter(|child| {
            matches!(
                child.kind(),
                SyntaxKind::Expr | SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
            )
        })
        .last()
}

pub(super) fn first_token_source_range(node: &Cst, kind: SyntaxKind) -> Option<SourceRange> {
    node.descendants_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == kind)
        .map(|token| crate::token_source_range(&token))
}

pub(super) fn catch_effect_op(path: Vec<Name>) -> CatchEffectOp {
    let Some((operation, family_path)) = path.split_last() else {
        return CatchEffectOp {
            path,
            family_path: Vec::new(),
            operation: None,
        };
    };
    let operation = operation.clone();
    let family_path = family_path.to_vec();
    if family_path.is_empty() {
        return CatchEffectOp {
            path,
            family_path: vec![operation],
            operation: None,
        };
    }
    CatchEffectOp {
        path,
        family_path,
        operation: Some(operation),
    }
}

pub(super) fn pat_covers_all(poly: &poly::expr::Arena, pat: PatId) -> bool {
    match poly.pat(pat) {
        Pat::Wild | Pat::Var(_) => true,
        Pat::Lit(Lit::Unit) => true,
        Pat::Tuple(items) => items.iter().all(|item| pat_covers_all(poly, *item)),
        Pat::Or(lhs, rhs) => pat_covers_all(poly, *lhs) || pat_covers_all(poly, *rhs),
        Pat::As(inner, _) => pat_covers_all(poly, *inner),
        Pat::Lit(_)
        | Pat::List { .. }
        | Pat::Record { .. }
        | Pat::PolyVariant(_, _)
        | Pat::Con(_, _)
        | Pat::Ref(_) => false,
    }
}
