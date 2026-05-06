use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::{ExprKind, TypedBlock, TypedExpr, TypedStmt};
use crate::lower::{LowerState, SyntaxNode};
use crate::types::{Neg, Pos};

/// IndentBlock / BraceGroup / Root をブロックとして lowering する。
///
/// 先行登録（pre-pass）→ 本体 lower（main-pass）の 2 フェーズ構成。
/// 各 stmt/tail のエフェクトを block.eff に合流させる。
pub fn lower_block(state: &mut LowerState, node: &SyntaxNode) -> TypedBlock {
    let mut items = Vec::new();
    collect_block_items(node, &mut items);
    lower_block_from_items(state, &items)
}

/// ブロック直下の要素をフラットに集める。
///
/// 既存の block lowering は IndentBlock / BraceGroup を同一ブロックとして展開していたため、
/// do 変換でも同じ粒度で suffix を切り出す。
pub(crate) fn collect_block_items(node: &SyntaxNode, out: &mut Vec<SyntaxNode>) {
    for child in node.children() {
        match child.kind() {
            SyntaxKind::IndentBlock | SyntaxKind::BraceGroup => collect_block_items(&child, out),
            _ => out.push(child),
        }
    }
}

pub(crate) fn lower_block_from_items(state: &mut LowerState, items: &[SyntaxNode]) -> TypedBlock {
    let tv = state.fresh_tv();
    let eff = state.fresh_tv();

    super::preregister_items_until_do(state, items);

    let mut stmts = Vec::new();
    let mut tail: Option<Box<TypedExpr>> = None;

    lower_block_items(state, items, &mut stmts, &mut tail);

    for stmt in &stmts {
        let stmt_eff = stmt_eff(stmt);
        if let Some(e) = stmt_eff {
            state.infer.constrain(Pos::Var(e), Neg::Var(eff));
        }
    }
    if let Some(t) = &tail {
        state.infer.constrain(Pos::Var(t.tv), Neg::Var(tv));
        state.infer.constrain(Pos::Var(t.eff), Neg::Var(eff));
    } else {
        state
            .infer
            .constrain(super::super::prim_type("unit"), Neg::Var(tv));
        state
            .infer
            .constrain(state.infer.arena.empty_pos_row, Neg::Var(eff));
    }

    TypedBlock {
        tv,
        eff,
        stmts,
        tail,
    }
}

pub(crate) fn lower_scoped_with_block_expr_with_tail(
    state: &mut LowerState,
    items: &[SyntaxNode],
    lower_tail: impl FnOnce(&mut LowerState) -> TypedExpr,
) -> TypedExpr {
    let public_names = with_public_binding_names(items);
    state.ctx.push_local();
    let mut prefix = state.with_force_local_bindings(|state| lower_block_from_items(state, items));
    if let Some(tail) = prefix.tail.take() {
        prefix.stmts.push(TypedStmt::Expr(*tail));
    }
    let with_frame = state.ctx.pop_local_frame();

    state.ctx.push_local();
    for name in public_names {
        if let Some(def) = with_frame.get(&name) {
            state.ctx.bind_local(name, *def);
        }
    }
    let tail = lower_tail(state);
    state.ctx.pop_local();

    block_expr_from_parts(state, prefix.stmts, tail)
}

fn block_expr_from_parts(
    state: &mut LowerState,
    stmts: Vec<TypedStmt>,
    tail: TypedExpr,
) -> TypedExpr {
    let tv = state.fresh_tv();
    let eff = state.fresh_tv();
    for stmt in &stmts {
        if let Some(stmt_eff) = stmt_eff(stmt) {
            state.infer.constrain(Pos::Var(stmt_eff), Neg::Var(eff));
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

fn with_public_binding_names(items: &[SyntaxNode]) -> Vec<crate::symbols::Name> {
    items
        .iter()
        .filter_map(|item| {
            if !matches!(item.kind(), SyntaxKind::Binding | SyntaxKind::OpDef) {
                return None;
            }
            let header = super::super::child_node(item, SyntaxKind::BindingHeader)
                .or_else(|| super::super::child_node(item, SyntaxKind::OpDefHeader))?;
            if !(super::super::has_token(&header, SyntaxKind::Our)
                || super::super::has_token(&header, SyntaxKind::Pub))
            {
                return None;
            }
            if item.kind() == SyntaxKind::OpDef {
                return super::super::header_value_name(&header);
            }
            let pat = super::super::child_node(&header, SyntaxKind::Pattern)?;
            super::super::direct_binding_name(&pat)
        })
        .collect()
}

fn stmt_eff(stmt: &TypedStmt) -> Option<crate::ids::TypeVar> {
    match stmt {
        TypedStmt::Let(_, expr) => Some(expr.eff),
        TypedStmt::Expr(expr) => Some(expr.eff),
        TypedStmt::Module(..) => None,
    }
}

fn lower_block_items(
    state: &mut LowerState,
    items: &[SyntaxNode],
    stmts: &mut Vec<TypedStmt>,
    tail: &mut Option<Box<TypedExpr>>,
) {
    fn flush_tail_into_stmt(stmts: &mut Vec<TypedStmt>, tail: &mut Option<Box<TypedExpr>>) {
        if let Some(expr) = tail.take() {
            stmts.push(TypedStmt::Expr(*expr));
        }
    }

    for (idx, child) in items.iter().enumerate() {
        match child.kind() {
            SyntaxKind::Binding | SyntaxKind::OpDef => {
                flush_tail_into_stmt(stmts, tail);
                if super::binding_is_do_binding(child) {
                    if let Some(expr) = super::lower_do_binding(state, child, &items[idx + 1..]) {
                        tail.replace(Box::new(expr));
                    }
                    break;
                }
                if let Some(stmt) = super::super::lower_binding(state, &child) {
                    let var_bindings = super::super::binding_var_sigils(child);
                    stmts.push(stmt);
                    if !var_bindings.is_empty() {
                        super::super::lower_var_binding_suffix(
                            state,
                            &var_bindings,
                            &items[idx + 1..],
                            stmts,
                            tail,
                        );
                        break;
                    }
                }
            }
            SyntaxKind::UseDecl => {
                flush_tail_into_stmt(stmts, tail);
                super::super::lower_use_decl(state, &child);
            }
            SyntaxKind::ModDecl => {
                flush_tail_into_stmt(stmts, tail);
                if let Some(stmt) = super::super::lower_mod_decl(state, &child) {
                    stmts.push(stmt);
                }
            }
            SyntaxKind::ActDecl => {
                flush_tail_into_stmt(stmts, tail);
                super::super::lower_act_decl(state, &child);
            }
            SyntaxKind::RoleDecl => {
                flush_tail_into_stmt(stmts, tail);
                super::super::lower_role_decl(state, &child);
            }
            SyntaxKind::ImplDecl => {
                flush_tail_into_stmt(stmts, tail);
                super::super::lower_impl_decl(state, &child);
            }
            SyntaxKind::CastDecl => {
                flush_tail_into_stmt(stmts, tail);
                super::super::lower_cast_decl(state, &child);
            }
            SyntaxKind::StructDecl => {
                flush_tail_into_stmt(stmts, tail);
                super::super::lower_struct_decl(state, &child);
            }
            SyntaxKind::EnumDecl => {
                flush_tail_into_stmt(stmts, tail);
                super::super::lower_enum_decl(state, &child);
            }
            SyntaxKind::TypeDecl => {
                flush_tail_into_stmt(stmts, tail);
                super::super::lower_type_decl(state, &child);
            }
            SyntaxKind::WhereClause => {
                flush_tail_into_stmt(stmts, tail);
                super::super::lower_where_clause(state, &child);
            }
            SyntaxKind::ForStmt => {
                flush_tail_into_stmt(stmts, tail);
                tail.replace(Box::new(super::lower_for_stmt(state, &child)));
            }
            SyntaxKind::Expr => {
                flush_tail_into_stmt(stmts, tail);
                if super::node_has_do_here(child) {
                    tail.replace(Box::new(super::lower_do_expr(
                        state,
                        child,
                        &items[idx + 1..],
                    )));
                    break;
                }
                tail.replace(Box::new(
                    super::lower_expr_with_synthetic_owner_if_top_level(state, &child),
                ));
            }
            _ => {}
        }
    }
}
