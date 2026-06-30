//! Projection bundle tail lowering.

use super::super::*;
use super::chain::qualified_field_selection_name;
use super::*;

impl<'a> ExprLowerer<'a> {
    pub(in crate::lowering) fn lower_projection_tuple_tail(
        &mut self,
        receiver: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        self.lower_projection_tail(receiver, |this, receiver| {
            this.lower_projection_tuple_body(receiver, node)
        })
    }

    pub(in crate::lowering) fn lower_projection_record_tail(
        &mut self,
        receiver: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        self.lower_projection_tail(receiver, |this, receiver| {
            this.lower_projection_record_body(receiver, node)
        })
    }

    fn lower_projection_tail(
        &mut self,
        receiver: Computation,
        lower_body: impl FnOnce(&mut Self, Computation) -> Result<Computation, LoweringError>,
    ) -> Result<Computation, LoweringError> {
        if !receiver.is_expansive() {
            return lower_body(self, receiver);
        }

        let before_locals = self.locals.len();
        let receiver_name = Name("#projection-receiver".into());
        let (receiver_pat, _) = self.bind_let_local_with_def(
            receiver_name.clone(),
            receiver.value,
            LocalCallReturnEffect::Annotated,
            Some(receiver.expr),
        );
        let receiver_local = self
            .locals
            .last()
            .cloned()
            .expect("projection receiver should be the last local");
        let local_receiver = self.lower_local_name(receiver_name, receiver_local, None);
        let body = lower_body(self, local_receiver);
        self.locals.truncate(before_locals);
        let body = body?;

        let value = self.fresh_type_var();
        let effect = self.fresh_type_var();
        self.subtype_var_to_var(receiver.effect, effect);
        self.subtype_var_to_var(body.effect, effect);
        self.subtype_var_to_var(body.value, value);
        let expr = self.session.poly.add_expr(Expr::Block(
            vec![Stmt::Let(Vis::My, receiver_pat, receiver.expr)],
            Some(body.expr),
        ));
        Ok(Computation::computation(expr, value, effect))
    }

    fn lower_projection_tuple_body(
        &mut self,
        receiver: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let group = projection_group(node, SyntaxKind::Paren)?;
        let item_nodes = group
            .children()
            .filter(|child| child.kind() == SyntaxKind::Expr)
            .collect::<Vec<_>>();
        match item_nodes.as_slice() {
            [] => Ok(self.unit_expr()),
            [expr] => self.lower_projected_expr(receiver, expr),
            _ => {
                let items = item_nodes
                    .iter()
                    .map(|expr| self.lower_projected_expr(receiver, expr))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.synthetic_tuple_value(items))
            }
        }
    }

    fn lower_projection_record_body(
        &mut self,
        receiver: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let group = projection_group(node, SyntaxKind::BraceGroup)?;
        let mut fields = Vec::new();
        for child in group.children() {
            match child.kind() {
                SyntaxKind::Expr => {
                    let name =
                        record_field_name(&child).ok_or(LoweringError::MissingRecordFieldName)?;
                    let value_node =
                        record_field_value(&child).ok_or(LoweringError::MissingRecordFieldValue)?;
                    let value = self.lower_projected_expr(receiver, &value_node)?;
                    fields.push((name.0, value));
                }
                SyntaxKind::ExprSpread => {
                    return Err(LoweringError::UnsupportedSyntax {
                        kind: SyntaxKind::ExprSpread,
                    });
                }
                _ => {}
            }
        }
        Ok(self.synthetic_record_value(fields))
    }

    fn lower_projected_expr(
        &mut self,
        receiver: Computation,
        expr: &Cst,
    ) -> Result<Computation, LoweringError> {
        let items = expr
            .children_with_tokens()
            .filter(|item| !item_is_trivia(item))
            .collect::<Vec<_>>();
        let (name, consumed) = projected_selection_name(&items)?;
        let mut acc = self.lower_synthetic_selection_at(
            receiver,
            name,
            item_slice_source_range(&items[..consumed]),
        );
        let mut index = consumed;
        while index < items.len() {
            match &items[index] {
                NodeOrToken::Node(child) if child.kind() == SyntaxKind::Field => {
                    let (name, path_tail_len) =
                        qualified_field_selection_name(child, &items[index + 1..])?;
                    acc = if path_tail_len == 0 {
                        self.lower_field_selection(acc, child)?
                    } else {
                        self.lower_synthetic_selection_at(
                            acc,
                            name,
                            super::tail::field_source_range(child),
                        )
                    };
                    index += 1 + path_tail_len;
                    continue;
                }
                NodeOrToken::Node(child) => acc = self.lower_tail_node(acc, child)?,
                NodeOrToken::Token(token) => {
                    return Err(LoweringError::UnsupportedSyntax { kind: token.kind() });
                }
            }
            index += 1;
        }
        Ok(acc)
    }
}

fn projection_group(node: &Cst, kind: SyntaxKind) -> Result<Cst, LoweringError> {
    node.children()
        .find(|child| child.kind() == kind)
        .ok_or(LoweringError::UnsupportedSyntax { kind: node.kind() })
}

fn projected_selection_name(items: &[CstItem]) -> Result<(String, usize), LoweringError> {
    let Some(NodeOrToken::Token(head)) = items.first() else {
        return Err(LoweringError::UnsupportedSyntax {
            kind: SyntaxKind::Expr,
        });
    };
    if head.kind() != SyntaxKind::Ident {
        return Err(LoweringError::UnsupportedSyntax { kind: head.kind() });
    }

    let mut path = vec![head.text().to_string()];
    let mut consumed = 1;
    for item in &items[1..] {
        let NodeOrToken::Node(path_sep) = item else {
            break;
        };
        if path_sep.kind() != SyntaxKind::PathSep {
            break;
        }
        let name = path_sep_name(path_sep).ok_or(LoweringError::UnsupportedSyntax {
            kind: SyntaxKind::PathSep,
        })?;
        path.push(name.0);
        consumed += 1;
    }
    Ok((path.join("::"), consumed))
}
