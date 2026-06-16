//! List literal lowering.
//!
//! List literals are lowered through the canonical list primitive operators:
//! empty, singleton, and merge. The element slot is shared for the whole
//! literal so spreads and singleton items contribute to the same list type.

use super::*;

#[derive(Clone)]
enum ListLiteralItem {
    Single(Cst),
    Spread(Cst),
}

impl<'a> ExprLowerer<'a> {
    /// Lower `[a, b, ...xs]` into balanced list primitive applications.
    pub(super) fn lower_list_literal(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let mut items = Vec::new();
        for child in node.children() {
            match child.kind() {
                SyntaxKind::Expr => items.push(ListLiteralItem::Single(child)),
                SyntaxKind::ExprSpread => {
                    let expr = child
                        .children()
                        .find(|child| child.kind() == SyntaxKind::Expr)
                        .ok_or(LoweringError::UnsupportedSyntax {
                            kind: SyntaxKind::ExprSpread,
                        })?;
                    items.push(ListLiteralItem::Spread(expr));
                }
                _ => {}
            }
        }
        let item = self.fresh_type_var();
        let list_path = self.builtin_op_con_path("list")?;
        self.build_list_literal(item, &list_path, &items)
    }

    fn build_list_literal(
        &mut self,
        item: TypeVar,
        list_path: &[String],
        items: &[ListLiteralItem],
    ) -> Result<Computation, LoweringError> {
        if items.is_empty() {
            let empty = self.list_empty_callee(item, list_path);
            let unit = self.unit_expr();
            return Ok(self.make_app(empty, unit));
        }
        if let [single] = items {
            return self.lower_list_literal_part(item, list_path, single);
        }
        let mid = items.len() / 2;
        let left = self.build_list_literal(item, list_path, &items[..mid])?;
        let right = self.build_list_literal(item, list_path, &items[mid..])?;
        let merge = self.list_merge_callee(item, list_path);
        let applied = self.make_app(merge, left);
        Ok(self.make_app(applied, right))
    }

    fn lower_list_literal_part(
        &mut self,
        item: TypeVar,
        list_path: &[String],
        part: &ListLiteralItem,
    ) -> Result<Computation, LoweringError> {
        match part {
            ListLiteralItem::Single(node) => {
                let value = self.lower_expr(node)?;
                let singleton = self.list_singleton_callee(value.value, list_path);
                Ok(self.make_app(singleton, value))
            }
            ListLiteralItem::Spread(node) => {
                let value = self.lower_expr(node)?;
                self.constrain_list_value(value.value, item, list_path);
                Ok(value)
            }
        }
    }

    fn list_empty_callee(&mut self, item: TypeVar, list_path: &[String]) -> Computation {
        let pos = {
            let arg = self.alloc_neg(primitive_neg_type("unit"));
            let arg_eff = self.never_neg();
            let ret_eff = self.alloc_pos(Pos::Bot);
            let ret = self.list_con_pos(item, list_path);
            let ret = self.alloc_pos(ret);
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            }
        };
        let neg = {
            let arg = self.alloc_pos(primitive_type("unit"));
            let arg_eff = self.alloc_pos(Pos::Bot);
            let ret_eff = self.never_neg();
            let ret = self.list_con_neg(item, list_path);
            let ret = self.alloc_neg(ret);
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            }
        };
        self.list_primitive_callee(PrimitiveOp::ListEmpty, pos, neg)
    }

    fn list_singleton_callee(&mut self, item: TypeVar, list_path: &[String]) -> Computation {
        let pos = {
            let arg = self.alloc_neg(Neg::Var(item));
            let arg_eff = self.never_neg();
            let ret_eff = self.alloc_pos(Pos::Bot);
            let ret = self.list_con_pos(item, list_path);
            let ret = self.alloc_pos(ret);
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            }
        };
        let neg = {
            let arg = self.alloc_pos(Pos::Var(item));
            let arg_eff = self.alloc_pos(Pos::Bot);
            let ret_eff = self.never_neg();
            let ret = self.list_con_neg(item, list_path);
            let ret = self.alloc_neg(ret);
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            }
        };
        self.list_primitive_callee(PrimitiveOp::ListSingleton, pos, neg)
    }

    fn list_merge_callee(&mut self, item: TypeVar, list_path: &[String]) -> Computation {
        let pos = {
            let ret = self.list_con_pos(item, list_path);
            let ret = self.alloc_pos(ret);
            let inner_arg = self.list_con_neg(item, list_path);
            let inner_arg = self.alloc_neg(inner_arg);
            let inner_arg_eff = self.never_neg();
            let inner_ret_eff = self.alloc_pos(Pos::Bot);
            let inner = Pos::Fun {
                arg: inner_arg,
                arg_eff: inner_arg_eff,
                ret_eff: inner_ret_eff,
                ret,
            };
            let inner = self.alloc_pos(inner);
            let arg = self.list_con_neg(item, list_path);
            let arg = self.alloc_neg(arg);
            let arg_eff = self.never_neg();
            let ret_eff = self.alloc_pos(Pos::Bot);
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret: inner,
            }
        };
        let neg = {
            let ret = self.list_con_neg(item, list_path);
            let ret = self.alloc_neg(ret);
            let inner_arg = self.list_con_pos(item, list_path);
            let inner_arg = self.alloc_pos(inner_arg);
            let inner_arg_eff = self.alloc_pos(Pos::Bot);
            let inner_ret_eff = self.never_neg();
            let inner = Neg::Fun {
                arg: inner_arg,
                arg_eff: inner_arg_eff,
                ret_eff: inner_ret_eff,
                ret,
            };
            let inner = self.alloc_neg(inner);
            let arg = self.list_con_pos(item, list_path);
            let arg = self.alloc_pos(arg);
            let arg_eff = self.alloc_pos(Pos::Bot);
            let ret_eff = self.never_neg();
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret: inner,
            }
        };
        self.list_primitive_callee(PrimitiveOp::ListMerge, pos, neg)
    }

    fn list_con_pos(&mut self, item: TypeVar, list_path: &[String]) -> Pos {
        let arg = self.invariant_var_arg(item);
        Pos::Con(list_path.to_vec(), vec![arg])
    }

    fn list_con_neg(&mut self, item: TypeVar, list_path: &[String]) -> Neg {
        let arg = self.invariant_var_arg(item);
        Neg::Con(list_path.to_vec(), vec![arg])
    }

    pub(super) fn constrain_list_value(
        &mut self,
        value: TypeVar,
        item: TypeVar,
        list_path: &[String],
    ) {
        let lower = self.list_con_pos(item, list_path);
        self.constrain_lower(value, lower);
        let upper = self.list_con_neg(item, list_path);
        self.constrain_upper(value, upper);
    }

    fn list_primitive_callee(&mut self, op: PrimitiveOp, lower: Pos, upper: Neg) -> Computation {
        let value = self.fresh_type_var();
        self.constrain_lower(value, lower);
        self.constrain_upper(value, upper);
        let effect = self.fresh_exact_pure_effect();
        let expr = self.session.poly.add_expr(Expr::PrimitiveOp(op));
        Computation::value(expr, value, effect)
    }
}
