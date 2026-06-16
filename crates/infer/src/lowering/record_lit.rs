//! Record literal and synthetic record value lowering.

use super::*;

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
            self.subtype_var_to_var(value.effect, result_effect);
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
        let fields = record_literal_fields(node);
        let mut lowered = Vec::with_capacity(fields.len());
        for field in fields {
            let name = record_field_name(&field).ok_or(LoweringError::MissingRecordFieldName)?;
            let value_node =
                record_field_value(&field).ok_or(LoweringError::MissingRecordFieldValue)?;
            let value = self.lower_expr(&value_node)?;
            lowered.push((name, value));
        }

        let result_value = self.fresh_type_var();
        let expansive = lowered.iter().any(|(_, value)| value.is_expansive());
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
            self.subtype_var_to_var(value.effect, result_effect);
        }
        self.constrain_lower(result_value, Pos::Record(record_fields));

        let expr_fields = lowered
            .into_iter()
            .map(|(name, value)| (name.0, value.expr))
            .collect();
        let expr = self.session.poly.add_expr(Expr::Record {
            fields: expr_fields,
            spread: RecordSpread::None,
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
