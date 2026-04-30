use rowan::TextRange;
use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::{ExprKind, Lit, TypedExpr};
use crate::diagnostic::{TypeOrigin, TypeOriginKind};
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::Name;
use crate::types::Neg;

use super::{apply_synthetic_field_selection, lower_expr, make_app, prim_type, resolve_path_expr};

pub(super) fn lower_number_token(
    state: &mut LowerState,
    text: &str,
    span: Option<TextRange>,
) -> TypedExpr {
    let tv = state.fresh_tv_with_origin(TypeOrigin {
        span,
        kind: TypeOriginKind::Literal,
        label: Some(text.to_string()),
    });
    let eff = state.fresh_exact_pure_eff_tv();
    let (kind, type_name) = if let Ok(n) = text.parse::<i64>() {
        (ExprKind::Lit(Lit::Int(n)), "int")
    } else if let Ok(f) = text.parse::<f64>() {
        (ExprKind::Lit(Lit::Float(f)), "float")
    } else {
        (ExprKind::Lit(Lit::Unit), "unit")
    };
    state.infer.constrain(prim_type(type_name), Neg::Var(tv));
    TypedExpr { tv, eff, kind }
}

pub(super) fn lower_string_lit(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let parts = collect_string_parts(state, node);
    if parts.iter().all(|part| matches!(part, StringPart::Text(_))) {
        let text = parts
            .into_iter()
            .map(|part| match part {
                StringPart::Text(text) => text,
                StringPart::Expr(_, _) => unreachable!(),
            })
            .collect();
        return string_lit_expr(state, text);
    }

    let mut lowered = None;
    for part in parts {
        let expr = match part {
            StringPart::Text(text) if text.is_empty() => continue,
            StringPart::Text(text) => string_lit_expr(state, text),
            StringPart::Expr(expr, fmt) => display_expr(state, expr, fmt, node),
        };
        lowered = Some(match lowered {
            Some(acc) => concat_expr(state, acc, expr),
            None => expr,
        });
    }

    lowered.unwrap_or_else(|| string_lit_expr(state, String::new()))
}

fn display_expr(
    state: &mut LowerState,
    expr: TypedExpr,
    fmt: Option<String>,
    node: &SyntaxNode,
) -> TypedExpr {
    let method_name = match fmt.as_deref() {
        Some("x") => Name("lower_hex".to_string()),
        Some("X") => Name("upper_hex".to_string()),
        _ => Name("show".to_string()),
    };
    let show = apply_synthetic_field_selection(state, expr, method_name, node);
    state.infer.constrain(prim_type("str"), Neg::Var(show.tv));
    show
}

fn string_lit_expr(state: &mut LowerState, text: String) -> TypedExpr {
    let tv = state.fresh_tv();
    let eff = state.fresh_exact_pure_eff_tv();
    state.infer.constrain(prim_type("str"), Neg::Var(tv));
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::Lit(Lit::Str(text)),
    }
}

fn concat_expr(state: &mut LowerState, lhs: TypedExpr, rhs: TypedExpr) -> TypedExpr {
    let concat = resolve_path_expr(
        state,
        vec![
            Name("std".to_string()),
            Name("str".to_string()),
            Name("concat".to_string()),
        ],
    );
    let app = make_app(state, concat, lhs);
    make_app(state, app, rhs)
}

enum StringPart {
    Text(String),
    Expr(TypedExpr, Option<String>),
}

fn collect_string_parts(state: &mut LowerState, node: &SyntaxNode) -> Vec<StringPart> {
    let mut parts = Vec::new();
    let mut text = String::new();
    let mut tokens = node.children_with_tokens().peekable();
    while let Some(item) = tokens.next() {
        if let Some(token) = item.as_token() {
            match token.kind() {
                SyntaxKind::StringText => text.push_str(token.text()),
                SyntaxKind::StringEscapeLead => {
                    text.push_str(&collect_escape_text(&mut tokens));
                }
                _ => {}
            }
            continue;
        }

        let Some(child) = item.as_node() else {
            continue;
        };
        if child.kind() != SyntaxKind::StringInterp {
            continue;
        }
        if !text.is_empty() {
            parts.push(StringPart::Text(std::mem::take(&mut text)));
        }

        let fmt = child.children_with_tokens().find_map(|item| {
            item.as_token()
                .filter(|t| t.kind() == SyntaxKind::StringInterpFormatText)
                .map(|t| t.text().to_string())
        });

        if let Some(expr) = child
            .children()
            .find(|child| child.kind() == SyntaxKind::Expr)
        {
            parts.push(StringPart::Expr(lower_expr(state, &expr), fmt));
        }
    }
    if !text.is_empty() {
        parts.push(StringPart::Text(text));
    }
    parts
}

fn collect_escape_text(
    tokens: &mut std::iter::Peekable<
        rowan::SyntaxElementChildren<yulang_parser::sink::YulangLanguage>,
    >,
) -> String {
    let Some(next) = tokens.next().and_then(|item| item.into_token()) else {
        return String::new();
    };
    match next.kind() {
        SyntaxKind::StringEscapeSimple => simple_escape_text(next.text()),
        SyntaxKind::StringEscapeUnicodeStart => collect_unicode_escape_text(tokens),
        _ => next.text().to_string(),
    }
}

fn simple_escape_text(text: &str) -> String {
    match text {
        "n" => "\n".to_string(),
        "r" => "\r".to_string(),
        "t" => "\t".to_string(),
        "\\" => "\\".to_string(),
        "\"" => "\"".to_string(),
        "0" => "\0".to_string(),
        other => other.to_string(),
    }
}

fn collect_unicode_escape_text(
    tokens: &mut std::iter::Peekable<
        rowan::SyntaxElementChildren<yulang_parser::sink::YulangLanguage>,
    >,
) -> String {
    let Some(hex) = tokens.next().and_then(|item| item.into_token()) else {
        return String::new();
    };
    if hex.kind() != SyntaxKind::StringEscapeUnicodeHex {
        return hex.text().to_string();
    }
    let value = u32::from_str_radix(hex.text(), 16)
        .ok()
        .and_then(char::from_u32)
        .unwrap_or(char::REPLACEMENT_CHARACTER);
    if matches!(
        tokens
            .peek()
            .and_then(|item| item.as_token())
            .map(|token| token.kind()),
        Some(SyntaxKind::StringEscapeUnicodeEnd)
    ) {
        tokens.next();
    }
    value.to_string()
}
