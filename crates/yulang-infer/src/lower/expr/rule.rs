use yulang_parser::lex::SyntaxKind;
use yulang_typed_ir::PrimitiveOp;

use crate::ast::expr::{ExprKind, PatKind, TypedBlock, TypedExpr, TypedPat, TypedStmt};
use crate::lower::stmt;
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::Name;
use crate::types::{Neg, Pos, RecordField};

use super::literal::string_lit_expr;
use super::{
    lower_expr, make_app, neg_prim_type, prim_type, resolve_bound_def_expr, resolve_path_expr,
};

pub(super) fn lower_rule_lit(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let body = match plain_rule_lit_text(node) {
        Some(text) => token_call(state, text),
        None => match rule_lit_parts(node) {
            Some(parts) => rule_lit_sequence(state, parts),
            None => unsupported_rule_sugar(state),
        },
    };
    unit_parser_lambda(state, body)
}

pub(super) fn lower_rule_expr(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let body = rule_expr_body(state, node)
        .map(|lowered| lowered.expr)
        .unwrap_or_else(|| unsupported_rule_sugar(state));
    unit_parser_lambda(state, body)
}

fn token_call(state: &mut LowerState, text: String) -> TypedExpr {
    let token = resolve_path_expr(
        state,
        ["std", "parse", "token"]
            .into_iter()
            .map(|segment| Name(segment.to_string()))
            .collect(),
    );
    let expected = string_lit_expr(state, text);
    make_app(state, token, expected)
}

fn word_call(state: &mut LowerState) -> TypedExpr {
    let word = resolve_path_expr(
        state,
        ["std", "parse", "word"]
            .into_iter()
            .map(|segment| Name(segment.to_string()))
            .collect(),
    );
    let unit = super::unit_expr(state);
    make_app(state, word, unit)
}

fn rule_lit_sequence(state: &mut LowerState, parts: Vec<RuleLitPart>) -> TypedExpr {
    let mut stmts = Vec::new();
    let mut fields = Vec::new();
    for part in parts {
        match part {
            RuleLitPart::Token(text) => {
                if !text.is_empty() {
                    stmts.push(TypedStmt::Expr(token_call(state, text)));
                }
            }
            RuleLitPart::Capture(name) => {
                let value = word_call(state);
                let (stmt, captured) = bind_synthetic_capture(state, name.clone(), value);
                stmts.push(stmt);
                fields.push((name, captured));
            }
        }
    }

    if fields.is_empty() {
        return unsupported_rule_sugar(state);
    }

    let record = record_expr(state, fields);
    block_expr_from_parts(state, stmts, record)
}

fn rule_expr_body(state: &mut LowerState, node: &SyntaxNode) -> Option<RuleLowered> {
    let group = node
        .children()
        .find(|child| child.kind() == SyntaxKind::BraceGroup)?;
    lower_rule_container_body(state, &group)
}

fn lower_rule_container_body(state: &mut LowerState, node: &SyntaxNode) -> Option<RuleLowered> {
    let branches = rule_branches(node);
    let mut lowered = branches
        .into_iter()
        .map(|branch| lower_rule_sequence(state, branch))
        .collect::<Option<Vec<_>>>()?
        .into_iter();
    let first = lowered.next()?;
    lowered.try_fold(first, |left, right| {
        let choice = std_parse_ref(state, "choice");
        let left_parser = unit_parser_lambda(state, left.expr);
        let right_parser = unit_parser_lambda(state, right.expr);
        let partial = make_app(state, choice, left_parser);
        let expr = make_app(state, partial, right_parser);
        let semantic =
            if left.semantic == RuleSemantic::Unit && right.semantic == RuleSemantic::Unit {
                RuleSemantic::Unit
            } else {
                RuleSemantic::Value
            };
        Some(RuleLowered { expr, semantic })
    })
}

fn lower_rule_sequence(state: &mut LowerState, items: Vec<SyntaxNode>) -> Option<RuleLowered> {
    let mut stmts = Vec::new();
    let mut fields = Vec::new();
    let mut value = None;

    for item in items {
        if let Some((name, parser)) = rule_expr_capture(&item) {
            let captured_value = lower_rule_item(state, &parser)?.expr;
            let (stmt, captured) = bind_synthetic_capture(state, name.clone(), captured_value);
            stmts.push(stmt);
            fields.push((name, captured));
            continue;
        }

        let lowered = lower_rule_item(state, &item)?;
        match lowered.semantic {
            RuleSemantic::Unit => stmts.push(TypedStmt::Expr(lowered.expr)),
            RuleSemantic::Record | RuleSemantic::Value => {
                if value.is_some() {
                    return None;
                }
                value = Some(lowered.expr);
            }
        }
    }

    let (tail, semantic) = if fields.is_empty() {
        match value {
            Some(value) => (value, RuleSemantic::Value),
            None => (super::unit_expr(state), RuleSemantic::Unit),
        }
    } else {
        if value.is_some() {
            return None;
        }
        (record_expr(state, fields), RuleSemantic::Record)
    };
    Some(RuleLowered {
        expr: block_expr_from_parts(state, stmts, tail),
        semantic,
    })
}

fn lower_rule_item(state: &mut LowerState, node: &SyntaxNode) -> Option<RuleLowered> {
    if let Some(quant) = rule_quant(node) {
        return lower_rule_quant(state, node, quant);
    }

    if let Some(text) = plain_string_expr_text(node) {
        return Some(RuleLowered {
            expr: token_call(state, text),
            semantic: RuleSemantic::Unit,
        });
    }

    if let Some(paren) = direct_child(node, SyntaxKind::Paren) {
        return lower_rule_container_body(state, &paren);
    }

    let parser = lower_expr(state, node);
    let unit = super::unit_expr(state);
    Some(RuleLowered {
        expr: make_app(state, parser, unit),
        semantic: RuleSemantic::Value,
    })
}

fn lower_rule_quant(
    state: &mut LowerState,
    node: &SyntaxNode,
    quant: SyntaxKind,
) -> Option<RuleLowered> {
    let base = lower_rule_quant_base(state, node)?;
    let parser = unit_parser_lambda(state, base.expr);
    let combinator = match quant {
        SyntaxKind::RuleQuantStar => "many",
        SyntaxKind::RuleQuantPlus => "some",
        SyntaxKind::RuleQuantStarLazy => "many_lazy",
        SyntaxKind::RuleQuantPlusLazy => "some_lazy",
        SyntaxKind::RuleQuantOpt => "optional",
        _ => return None,
    };
    let combinator = std_parse_ref(state, combinator);
    let expr = make_app(state, combinator, parser);
    let (expr, semantic) = if base.semantic == RuleSemantic::Unit {
        (discard_expr_to_unit(state, expr), RuleSemantic::Unit)
    } else {
        (expr, RuleSemantic::Value)
    };
    Some(RuleLowered { expr, semantic })
}

fn discard_expr_to_unit(state: &mut LowerState, expr: TypedExpr) -> TypedExpr {
    let pat = TypedPat {
        tv: state.fresh_tv(),
        kind: PatKind::Wild,
    };
    stmt::connect_let_pattern(state, &pat, expr.tv, expr.eff, None, false);
    let unit = super::unit_expr(state);
    block_expr_from_parts(state, vec![TypedStmt::Let(pat, expr)], unit)
}

fn lower_rule_quant_base(state: &mut LowerState, node: &SyntaxNode) -> Option<RuleLowered> {
    if let Some(text) = plain_string_expr_text(node) {
        return Some(RuleLowered {
            expr: token_call(state, text),
            semantic: RuleSemantic::Unit,
        });
    }
    if let Some(paren) = direct_child(node, SyntaxKind::Paren) {
        return lower_rule_container_body(state, &paren);
    }
    if let Some(parser) = rule_parser_ref_expr(state, node) {
        let unit = super::unit_expr(state);
        return Some(RuleLowered {
            expr: make_app(state, parser, unit),
            semantic: RuleSemantic::Value,
        });
    }
    None
}

fn std_parse_ref(state: &mut LowerState, name: &str) -> TypedExpr {
    resolve_path_expr(
        state,
        ["std", "parse", name]
            .into_iter()
            .map(|segment| Name(segment.to_string()))
            .collect(),
    )
}

fn bind_synthetic_capture(
    state: &mut LowerState,
    field_name: Name,
    value: TypedExpr,
) -> (TypedStmt, TypedExpr) {
    let def = state.fresh_def();
    let def_tv = state.fresh_tv();
    state.register_def_tv(def, def_tv);
    state.mark_let_bound_def(def);
    state.register_def_name(def, Name(format!("#rule-capture-{}", field_name.0)));
    if let Some(owner) = state.current_owner {
        state.register_def_owner(def, owner);
    }

    let pat = TypedPat {
        tv: state.fresh_tv(),
        kind: PatKind::As(
            Box::new(TypedPat {
                tv: state.fresh_tv(),
                kind: PatKind::Wild,
            }),
            def,
        ),
    };
    stmt::connect_let_pattern(state, &pat, value.tv, value.eff, None, false);
    let captured = resolve_bound_def_expr(state, def);
    (TypedStmt::Let(pat, value), captured)
}

fn record_expr(state: &mut LowerState, fields: Vec<(Name, TypedExpr)>) -> TypedExpr {
    let tv = state.fresh_tv();
    let eff = state.fresh_tv();
    let record_fields = fields
        .iter()
        .map(|(name, expr)| RecordField::required(name.clone(), Pos::Var(expr.tv)))
        .collect();
    state
        .infer
        .constrain(state.pos_record(record_fields), Neg::Var(tv));
    state
        .infer
        .constrain(state.infer.arena.empty_pos_row, Neg::Var(eff));
    for (_, expr) in &fields {
        state.infer.constrain(Pos::Var(expr.eff), Neg::Var(eff));
    }
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::Record {
            fields,
            spread: None,
        },
    }
}

fn unit_parser_lambda(state: &mut LowerState, body: TypedExpr) -> TypedExpr {
    let arg = stmt::make_arg_pat_info(state, stmt::HeaderArg::Unit);
    stmt::wrap_header_lambdas(state, body, vec![arg])
}

fn block_expr_from_parts(
    state: &mut LowerState,
    stmts: Vec<TypedStmt>,
    tail: TypedExpr,
) -> TypedExpr {
    let tv = state.fresh_tv();
    let eff = state.fresh_tv();
    for stmt in &stmts {
        match stmt {
            TypedStmt::Let(_, expr) | TypedStmt::Expr(expr) => {
                state.infer.constrain(Pos::Var(expr.eff), Neg::Var(eff));
            }
            TypedStmt::Module(..) => {}
        }
    }
    state.infer.constrain(Pos::Var(tail.tv), Neg::Var(tv));
    state.infer.constrain(Pos::Var(tail.eff), Neg::Var(eff));

    TypedExpr {
        tv,
        eff,
        kind: ExprKind::Block(TypedBlock {
            tv,
            eff,
            stmts,
            tail: Some(Box::new(tail)),
        }),
    }
}

fn unsupported_rule_sugar(state: &mut LowerState) -> TypedExpr {
    let tv = state.fresh_tv();
    let eff = state.fresh_exact_pure_eff_tv();
    state.infer.constrain(prim_type("never"), Neg::Var(tv));
    state.infer.constrain(Pos::Var(tv), neg_prim_type("never"));
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::PrimitiveOp(PrimitiveOp::YadaYada),
    }
}

fn plain_rule_lit_text(node: &SyntaxNode) -> Option<String> {
    if node.children().any(|child| {
        matches!(
            child.kind(),
            SyntaxKind::RuleLitInterp | SyntaxKind::RuleLazyCapture
        )
    }) {
        return None;
    }

    Some(
        node.descendants_with_tokens()
            .filter_map(|item| item.into_token())
            .filter(|token| token.kind() == SyntaxKind::RuleLitText)
            .map(|token| token.text().to_string())
            .collect(),
    )
}

fn rule_lit_parts(node: &SyntaxNode) -> Option<Vec<RuleLitPart>> {
    let mut parts = Vec::new();
    for item in node.children_with_tokens() {
        match item.kind() {
            SyntaxKind::RuleLitText => {
                let token = item.into_token()?;
                parts.push(RuleLitPart::Token(token.text().to_string()));
            }
            SyntaxKind::RuleLazyCapture => {
                let capture = item.into_node()?;
                parts.push(RuleLitPart::Capture(lazy_capture_name(&capture)?));
            }
            SyntaxKind::RuleLitStart | SyntaxKind::RuleLitEnd => {}
            _ => return None,
        }
    }
    Some(parts)
}

fn lazy_capture_name(node: &SyntaxNode) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::RuleLitText)
        .map(|token| Name(token.text().to_string()))
}

enum RuleLitPart {
    Token(String),
    Capture(Name),
}

struct RuleLowered {
    expr: TypedExpr,
    semantic: RuleSemantic,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum RuleSemantic {
    Unit,
    Record,
    Value,
}

fn rule_branches(node: &SyntaxNode) -> Vec<Vec<SyntaxNode>> {
    let mut branches = vec![Vec::new()];
    for child in node.children() {
        match child.kind() {
            SyntaxKind::Expr => {
                if let Some(branch) = branches.last_mut() {
                    branch.push(child);
                }
            }
            SyntaxKind::Separator => branches.push(Vec::new()),
            _ => {}
        }
    }
    branches
}

fn rule_expr_capture(node: &SyntaxNode) -> Option<(Name, SyntaxNode)> {
    let name = node
        .children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::Ident)
        .map(|token| Name(token.text().to_string()))?;
    let parser = node
        .children()
        .find(|child| child.kind() == SyntaxKind::RuleCapture)?
        .children()
        .find(|child| child.kind() == SyntaxKind::Expr)?;
    Some((name, parser))
}

fn rule_quant(node: &SyntaxNode) -> Option<SyntaxKind> {
    node.children()
        .find(|child| child.kind() == SyntaxKind::RuleQuant)?
        .children_with_tokens()
        .filter_map(|item| item.into_token())
        .find_map(|token| match token.kind() {
            SyntaxKind::RuleQuantStar
            | SyntaxKind::RuleQuantPlus
            | SyntaxKind::RuleQuantStarLazy
            | SyntaxKind::RuleQuantPlusLazy
            | SyntaxKind::RuleQuantOpt => Some(token.kind()),
            _ => None,
        })
}

fn direct_child(node: &SyntaxNode, kind: SyntaxKind) -> Option<SyntaxNode> {
    node.children().find(|child| child.kind() == kind)
}

fn rule_parser_ref_expr(state: &mut LowerState, node: &SyntaxNode) -> Option<TypedExpr> {
    let mut segments = Vec::new();
    for item in node.children_with_tokens() {
        match item.kind() {
            SyntaxKind::Ident if segments.is_empty() => {
                let token = item.into_token()?;
                segments.push(Name(token.text().to_string()));
            }
            SyntaxKind::PathSep => {
                let path_sep = item.into_node()?;
                let name = path_sep
                    .children_with_tokens()
                    .filter_map(|item| item.into_token())
                    .find(|token| token.kind() == SyntaxKind::Ident)
                    .map(|token| Name(token.text().to_string()))?;
                segments.push(name);
            }
            SyntaxKind::RuleQuant => {}
            _ => return None,
        }
    }
    if segments.is_empty() {
        None
    } else {
        Some(resolve_path_expr(state, segments))
    }
}

fn plain_string_expr_text(node: &SyntaxNode) -> Option<String> {
    let mut strings = node
        .children()
        .filter(|child| child.kind() == SyntaxKind::StringLit);
    let first = strings.next()?;
    if strings.next().is_some() {
        return None;
    }
    plain_string_lit_text(&first)
}

fn plain_string_lit_text(node: &SyntaxNode) -> Option<String> {
    if node
        .children()
        .any(|child| child.kind() == SyntaxKind::StringInterp)
    {
        return None;
    }

    Some(
        node.descendants_with_tokens()
            .filter_map(|item| item.into_token())
            .filter(|token| token.kind() == SyntaxKind::StringText)
            .map(|token| token.text().to_string())
            .collect(),
    )
}
