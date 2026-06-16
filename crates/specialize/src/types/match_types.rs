use super::*;

impl<'a> SchemeMaterializer<'a> {
    pub(super) fn match_pos(
        &mut self,
        id: PosId,
        expected: &Type,
        context: TypeContext,
    ) -> Result<(), SpecializeError> {
        match self.arena.pos(id) {
            Pos::Var(var) => self.bind_var(*var, expected),
            Pos::Con(path, args) => {
                let Type::Con {
                    path: expected_path,
                    args: expected_args,
                } = expected
                else {
                    return Ok(());
                };
                if path != expected_path || args.len() != expected_args.len() {
                    return Ok(());
                }
                for (index, (arg, expected)) in args.iter().zip(expected_args).enumerate() {
                    self.match_neu(*arg, expected, con_arg_context(path, index))?;
                }
                Ok(())
            }
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let Type::Fun {
                    arg: expected_arg,
                    arg_effect: expected_arg_eff,
                    ret_effect: expected_ret_eff,
                    ret: expected_ret,
                } = expected
                else {
                    return Ok(());
                };
                let (expected_arg, expected_arg_eff) =
                    split_runtime_shape(expected_arg, expected_arg_eff);
                let (expected_ret, expected_ret_eff) =
                    split_runtime_shape(expected_ret, expected_ret_eff);
                self.match_neg(*arg, &expected_arg, TypeContext::Value)?;
                self.match_neg(*arg_eff, &expected_arg_eff, TypeContext::Effect)?;
                self.match_pos(*ret_eff, &expected_ret_eff, TypeContext::Effect)?;
                self.match_pos(*ret, &expected_ret, TypeContext::Value)
            }
            Pos::Record(fields) => {
                let Type::Record(expected_fields) = expected else {
                    return Ok(());
                };
                for (field, expected) in fields.iter().zip(expected_fields) {
                    if field.name == expected.name {
                        self.match_pos(field.value, &expected.value, TypeContext::Value)?;
                    }
                }
                Ok(())
            }
            Pos::RecordTailSpread { fields, .. } | Pos::RecordHeadSpread { fields, .. } => {
                let Type::Record(expected_fields) = expected else {
                    return Ok(());
                };
                for field in fields {
                    if let Some(expected) =
                        expected_fields.iter().find(|item| item.name == field.name)
                    {
                        self.match_pos(field.value, &expected.value, TypeContext::Value)?;
                    }
                }
                Ok(())
            }
            Pos::PolyVariant(variants) => {
                let Type::PolyVariant(expected_variants) = expected else {
                    return Ok(());
                };
                for (name, payloads) in variants {
                    let Some(expected) = expected_variants.iter().find(|item| item.name == *name)
                    else {
                        continue;
                    };
                    for (payload, expected) in payloads.iter().zip(&expected.payloads) {
                        self.match_pos(*payload, expected, TypeContext::Value)?;
                    }
                }
                Ok(())
            }
            Pos::Tuple(items) => {
                let Type::Tuple(expected_items) = expected else {
                    return Ok(());
                };
                for (item, expected) in items.iter().zip(expected_items) {
                    self.match_pos(*item, expected, TypeContext::Value)?;
                }
                Ok(())
            }
            Pos::Row(items) => {
                let Type::EffectRow(expected_items) = expected else {
                    return Ok(());
                };
                for (item, expected) in items.iter().zip(expected_items) {
                    self.match_pos(*item, expected, TypeContext::Effect)?;
                }
                Ok(())
            }
            Pos::Stack { .. } => Ok(()),
            Pos::NonSubtract(inner, _) => self.match_pos(*inner, expected, context),
            Pos::Union(left, right) => {
                self.match_pos(*left, expected, context)?;
                self.match_pos(*right, expected, context)
            }
            Pos::Bot => Ok(()),
        }
    }

    pub(super) fn match_neg(
        &mut self,
        id: NegId,
        expected: &Type,
        context: TypeContext,
    ) -> Result<(), SpecializeError> {
        match self.arena.neg(id) {
            Neg::Var(var) => self.bind_var(*var, expected),
            Neg::Con(path, args) => {
                let Type::Con {
                    path: expected_path,
                    args: expected_args,
                } = expected
                else {
                    return Ok(());
                };
                if path != expected_path || args.len() != expected_args.len() {
                    return Ok(());
                }
                for (index, (arg, expected)) in args.iter().zip(expected_args).enumerate() {
                    self.match_neu(*arg, expected, con_arg_context(path, index))?;
                }
                Ok(())
            }
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let Type::Fun {
                    arg: expected_arg,
                    arg_effect: expected_arg_eff,
                    ret_effect: expected_ret_eff,
                    ret: expected_ret,
                } = expected
                else {
                    return Ok(());
                };
                let (expected_arg, expected_arg_eff) =
                    split_runtime_shape(expected_arg, expected_arg_eff);
                let (expected_ret, expected_ret_eff) =
                    split_runtime_shape(expected_ret, expected_ret_eff);
                self.match_pos(*arg, &expected_arg, TypeContext::Value)?;
                self.match_pos(*arg_eff, &expected_arg_eff, TypeContext::Effect)?;
                self.match_neg(*ret_eff, &expected_ret_eff, TypeContext::Effect)?;
                self.match_neg(*ret, &expected_ret, TypeContext::Value)
            }
            Neg::Record(fields) => {
                let Type::Record(expected_fields) = expected else {
                    return Ok(());
                };
                for field in fields {
                    if let Some(expected) =
                        expected_fields.iter().find(|item| item.name == field.name)
                    {
                        self.match_neg(field.value, &expected.value, TypeContext::Value)?;
                    }
                }
                Ok(())
            }
            Neg::PolyVariant(variants) => {
                let Type::PolyVariant(expected_variants) = expected else {
                    return Ok(());
                };
                for (name, payloads) in variants {
                    let Some(expected) = expected_variants.iter().find(|item| item.name == *name)
                    else {
                        continue;
                    };
                    for (payload, expected) in payloads.iter().zip(&expected.payloads) {
                        self.match_neg(*payload, expected, TypeContext::Value)?;
                    }
                }
                Ok(())
            }
            Neg::Tuple(items) => {
                let Type::Tuple(expected_items) = expected else {
                    return Ok(());
                };
                for (item, expected) in items.iter().zip(expected_items) {
                    self.match_neg(*item, expected, TypeContext::Value)?;
                }
                Ok(())
            }
            Neg::Row(items, tail) => {
                let Type::EffectRow(expected_items) = expected else {
                    return Ok(());
                };
                for (item, expected) in items.iter().zip(expected_items) {
                    self.match_neg(*item, expected, TypeContext::Effect)?;
                }
                if let Some(expected_tail) = expected_items.get(items.len()) {
                    self.match_neg(*tail, expected_tail, TypeContext::Effect)?;
                }
                Ok(())
            }
            Neg::Stack { .. } => Ok(()),
            Neg::Intersection(left, right) => {
                self.match_neg(*left, expected, context)?;
                self.match_neg(*right, expected, context)
            }
            Neg::Top | Neg::Bot => Ok(()),
        }
    }

    pub(super) fn match_neu(
        &mut self,
        id: NeuId,
        expected: &Type,
        context: TypeContext,
    ) -> Result<(), SpecializeError> {
        match self.arena.neu(id) {
            Neu::Bounds(lower, upper) => {
                self.match_pos(*lower, expected, context)?;
                self.match_neg(*upper, expected, context)
            }
            Neu::Con(path, args) => {
                let Type::Con {
                    path: expected_path,
                    args: expected_args,
                } = expected
                else {
                    return Ok(());
                };
                if path != expected_path || args.len() != expected_args.len() {
                    return Ok(());
                }
                for (index, (arg, expected)) in args.iter().zip(expected_args).enumerate() {
                    self.match_neu(*arg, expected, con_arg_context(path, index))?;
                }
                Ok(())
            }
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let Type::Fun {
                    arg: expected_arg,
                    arg_effect: expected_arg_eff,
                    ret_effect: expected_ret_eff,
                    ret: expected_ret,
                } = expected
                else {
                    return Ok(());
                };
                let (expected_arg, expected_arg_eff) =
                    split_runtime_shape(expected_arg, expected_arg_eff);
                let (expected_ret, expected_ret_eff) =
                    split_runtime_shape(expected_ret, expected_ret_eff);
                self.match_neu(*arg, &expected_arg, TypeContext::Value)?;
                self.match_neu(*arg_eff, &expected_arg_eff, TypeContext::Effect)?;
                self.match_neu(*ret_eff, &expected_ret_eff, TypeContext::Effect)?;
                self.match_neu(*ret, &expected_ret, TypeContext::Value)
            }
            Neu::Record(fields) => {
                let Type::Record(expected_fields) = expected else {
                    return Ok(());
                };
                for field in fields {
                    if let Some(expected) =
                        expected_fields.iter().find(|item| item.name == field.name)
                    {
                        self.match_neu(field.value, &expected.value, TypeContext::Value)?;
                    }
                }
                Ok(())
            }
            Neu::PolyVariant(variants) => {
                let Type::PolyVariant(expected_variants) = expected else {
                    return Ok(());
                };
                for (name, payloads) in variants {
                    let Some(expected) = expected_variants.iter().find(|item| item.name == *name)
                    else {
                        continue;
                    };
                    for (payload, expected) in payloads.iter().zip(&expected.payloads) {
                        self.match_neu(*payload, expected, TypeContext::Value)?;
                    }
                }
                Ok(())
            }
            Neu::Tuple(items) => {
                let Type::Tuple(expected_items) = expected else {
                    return Ok(());
                };
                for (item, expected) in items.iter().zip(expected_items) {
                    self.match_neu(*item, expected, TypeContext::Value)?;
                }
                Ok(())
            }
        }
    }
}
