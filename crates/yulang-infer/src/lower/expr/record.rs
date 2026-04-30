use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::{ExprKind, RecordSpread, TypedExpr};
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::Name;
use crate::types::{Neg, Pos};

use super::lower_expr;

pub(super) fn lower_record_literal(state: &mut LowerState, node: &SyntaxNode) -> Option<TypedExpr> {
    let lowered = lower_record_literal_fields(state, node)?;
    if lowered.fields.is_empty() && lowered.spread.is_none() {
        return None;
    }

    let tv = state.fresh_tv();
    let eff = state.fresh_tv();
    let record_fields = lowered
        .fields
        .iter()
        .map(|(name, expr)| crate::types::RecordField::required(name.clone(), Pos::Var(expr.tv)))
        .collect::<Vec<_>>();
    let pos = match lowered.spread.as_ref() {
        None => state.pos_record(record_fields),
        Some(LoweredRecordSpread::Head(expr)) => {
            state.pos_record_head_spread(Pos::Var(expr.tv), record_fields)
        }
        Some(LoweredRecordSpread::Tail(expr)) => {
            state.pos_record_tail_spread(record_fields, Pos::Var(expr.tv))
        }
    };
    state.infer.constrain(pos, Neg::Var(tv));
    state
        .infer
        .constrain(state.infer.arena.empty_pos_row, Neg::Var(eff));
    for (_, expr) in &lowered.fields {
        state.infer.constrain(Pos::Var(expr.eff), Neg::Var(eff));
    }
    if let Some(spread) = &lowered.spread {
        let expr = match spread {
            LoweredRecordSpread::Head(expr) | LoweredRecordSpread::Tail(expr) => expr,
        };
        state.infer.constrain(Pos::Var(expr.eff), Neg::Var(eff));
    }

    Some(TypedExpr {
        tv,
        eff,
        kind: ExprKind::Record {
            fields: lowered.fields,
            spread: lowered.spread.map(|spread| match spread {
                LoweredRecordSpread::Head(expr) => RecordSpread::Head(Box::new(expr)),
                LoweredRecordSpread::Tail(expr) => RecordSpread::Tail(Box::new(expr)),
            }),
        },
    })
}

fn lower_record_literal_fields(
    state: &mut LowerState,
    node: &SyntaxNode,
) -> Option<LoweredRecordLiteral> {
    if node.children().any(|child| {
        !matches!(child.kind(), SyntaxKind::Expr | SyntaxKind::Separator)
            && !(child.kind() == SyntaxKind::InvalidToken && child.to_string().contains(','))
    }) {
        return None;
    }
    let has_colon = node
        .descendants_with_tokens()
        .filter_map(|item| item.into_token())
        .any(|tok| tok.kind() == SyntaxKind::Colon);
    let exprs = node
        .children()
        .filter(|child| child.kind() == SyntaxKind::Expr)
        .collect::<Vec<_>>();
    if !has_colon && !exprs.iter().any(|expr| is_record_spread_expr(expr)) {
        return None;
    }

    let mut spread = None;
    let mut field_exprs = exprs.as_slice();
    if let Some(first) = exprs.first() {
        if is_record_spread_expr(first) {
            spread = Some(LoweredRecordSpread::Head(lower_record_spread_expr(
                state, first,
            )?));
            field_exprs = &exprs[1..];
        }
    }
    if let Some(last) = field_exprs.last() {
        if is_record_spread_expr(last) {
            if spread.is_some() {
                return None;
            }
            spread = Some(LoweredRecordSpread::Tail(lower_record_spread_expr(
                state, last,
            )?));
            field_exprs = &field_exprs[..field_exprs.len().saturating_sub(1)];
        }
    }

    let mut fields = Vec::new();
    let mut i = 0;
    while i < field_exprs.len() {
        if let Some(field) = lower_inline_record_field_expr(state, &field_exprs[i]) {
            fields.push(field);
            i += 1;
            continue;
        }
        let name = first_expr_ident(&field_exprs[i])?;
        let value = field_exprs.get(i + 1)?;
        fields.push((name, lower_expr(state, value)));
        i += 2;
    }
    Some(LoweredRecordLiteral { fields, spread })
}

fn is_record_spread_expr(node: &SyntaxNode) -> bool {
    node.to_string().trim_start().starts_with("..")
}

fn lower_record_spread_expr(state: &mut LowerState, node: &SyntaxNode) -> Option<TypedExpr> {
    let prefix = node
        .children()
        .find(|child| child.kind() == SyntaxKind::PrefixNode)?;
    if !prefix.to_string().trim_start().starts_with("..") {
        return None;
    }
    let inner = prefix
        .children()
        .find(|child| child.kind() == SyntaxKind::Expr)?;
    Some(lower_expr(state, &inner))
}

fn lower_inline_record_field_expr(
    state: &mut LowerState,
    node: &SyntaxNode,
) -> Option<(Name, TypedExpr)> {
    if node
        .children()
        .any(|child| child.kind() == SyntaxKind::PathSep)
    {
        return None;
    }
    let name = first_expr_ident(node)?;
    let suffix = node
        .children()
        .find(|child| child.kind() == SyntaxKind::ApplyColon)?;
    let value = suffix
        .children()
        .find(|child| child.kind() == SyntaxKind::Expr)?;
    Some((name, lower_expr(state, &value)))
}

fn first_expr_ident(node: &SyntaxNode) -> Option<Name> {
    node.descendants_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| {
            matches!(
                t.kind(),
                SyntaxKind::Ident
                    | SyntaxKind::SigilIdent
                    | SyntaxKind::Prefix
                    | SyntaxKind::Infix
                    | SyntaxKind::Suffix
                    | SyntaxKind::Nullfix
            )
        })
        .map(|t| Name(t.text().to_string()))
}

struct LoweredRecordLiteral {
    fields: Vec<(Name, TypedExpr)>,
    spread: Option<LoweredRecordSpread>,
}

enum LoweredRecordSpread {
    Head(TypedExpr),
    Tail(TypedExpr),
}
