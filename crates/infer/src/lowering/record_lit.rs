//! Record literal and synthetic record value lowering.

use super::*;

enum RecordLiteralItem {
    Field(Cst),
    Spread(Cst),
}

impl<'a> ExprLowerer<'a> {
    pub(super) fn synthetic_record_value(
        &mut self,
        fields: Vec<(String, Computation)>,
    ) -> Computation {
        let result_value = self.fresh_type_var();
        let expansive = fields.iter().any(|(_, value)| value.is_expansive());
        let result_effect = if expansive {
            self.fresh_type_var()
        } else {
            self.fresh_exact_pure_effect()
        };
        let record_fields = fields
            .iter()
            .map(|(name, value)| RecordField {
                name: name.clone(),
                value: self.alloc_pos(Pos::Var(value.value)),
                optional: false,
            })
            .collect::<Vec<_>>();
        for (_, value) in &fields {
            self.connect_effect_var_to_var(value.effect, result_effect);
        }
        self.constrain_lower(result_value, Pos::Record(record_fields));

        let expr_fields = fields
            .into_iter()
            .map(|(name, value)| (name, value.expr))
            .collect();
        let expr = self.session.poly.add_expr(Expr::Record {
            fields: expr_fields,
            spread: RecordSpread::None,
        });
        Computation::new(
            expr,
            result_value,
            result_effect,
            if expansive {
                Evaluation::Computation
            } else {
                Evaluation::Value
            },
        )
    }

    pub(super) fn lower_record_literal(
        &mut self,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let items = record_literal_items(node)?;
        let mut lowered = Vec::new();
        let mut spread = None;
        for item in items {
            match item {
                RecordLiteralItem::Field(field) => {
                    let name =
                        record_field_name(&field).ok_or(LoweringError::MissingRecordFieldName)?;
                    let value_node =
                        record_field_value(&field).ok_or(LoweringError::MissingRecordFieldValue)?;
                    let value = self.lower_expr(&value_node)?;
                    lowered.push((name, value));
                }
                RecordLiteralItem::Spread(expr) => {
                    if spread.is_some() {
                        return Err(LoweringError::UnsupportedSyntax {
                            kind: SyntaxKind::ExprSpread,
                        });
                    }
                    let is_head = lowered.is_empty();
                    spread = Some((is_head, self.lower_expr(&expr)?));
                }
            }
        }

        let result_value = self.fresh_type_var();
        let expansive = lowered.iter().any(|(_, value)| value.is_expansive())
            || spread
                .as_ref()
                .is_some_and(|(_, value)| value.is_expansive());
        let result_effect = if expansive {
            self.fresh_type_var()
        } else {
            self.fresh_exact_pure_effect()
        };
        let record_fields = lowered
            .iter()
            .map(|(name, value)| RecordField {
                name: name.0.clone(),
                value: self.alloc_pos(Pos::Var(value.value)),
                optional: false,
            })
            .collect::<Vec<_>>();
        for (_, value) in &lowered {
            self.connect_effect_var_to_var(value.effect, result_effect);
        }
        if let Some((_, value)) = &spread {
            self.connect_effect_var_to_var(value.effect, result_effect);
        }
        let lower = match &spread {
            Some((true, value)) => Pos::RecordHeadSpread {
                tail: self.alloc_pos(Pos::Var(value.value)),
                fields: record_fields.clone(),
            },
            Some((false, value)) => Pos::RecordTailSpread {
                fields: record_fields.clone(),
                tail: self.alloc_pos(Pos::Var(value.value)),
            },
            None => Pos::Record(record_fields),
        };
        self.constrain_lower(result_value, lower);

        let expr_fields = lowered
            .into_iter()
            .map(|(name, value)| (name.0, value.expr))
            .collect();
        let expr_spread = match spread {
            Some((true, value)) => RecordSpread::Head(value.expr),
            Some((false, value)) => RecordSpread::Tail(value.expr),
            None => RecordSpread::None,
        };
        let expr = self.session.poly.add_expr(Expr::Record {
            fields: expr_fields,
            spread: expr_spread,
        });
        Ok(Computation::new(
            expr,
            result_value,
            result_effect,
            if expansive {
                Evaluation::Computation
            } else {
                Evaluation::Value
            },
        ))
    }
}

fn record_literal_items(node: &Cst) -> Result<Vec<RecordLiteralItem>, LoweringError> {
    let mut items = Vec::new();
    for child in node.children() {
        match child.kind() {
            SyntaxKind::Expr => items.push(RecordLiteralItem::Field(child)),
            SyntaxKind::ExprSpread => {
                let expr = child
                    .children()
                    .find(|child| child.kind() == SyntaxKind::Expr)
                    .ok_or(LoweringError::UnsupportedSyntax {
                        kind: SyntaxKind::ExprSpread,
                    })?;
                items.push(RecordLiteralItem::Spread(expr));
            }
            _ => {}
        }
    }
    Ok(items)
}
