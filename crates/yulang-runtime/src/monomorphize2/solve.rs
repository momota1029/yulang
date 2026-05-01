use std::collections::BTreeMap;

use super::*;

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct DemandSubstitution {
    pub values: BTreeMap<u32, DemandSignature>,
    pub cores: BTreeMap<u32, DemandCoreType>,
    pub effects: BTreeMap<u32, DemandEffect>,
}

impl DemandSubstitution {
    pub fn apply_signature(&self, signature: &DemandSignature) -> DemandSignature {
        match signature {
            DemandSignature::Hole(id) => self
                .values
                .get(id)
                .map(|signature| self.apply_signature(signature))
                .unwrap_or(DemandSignature::Hole(*id)),
            DemandSignature::Core(ty) => DemandSignature::Core(self.apply_core_type(ty)),
            DemandSignature::Fun { param, ret } => DemandSignature::Fun {
                param: Box::new(self.apply_signature(param)),
                ret: Box::new(self.apply_signature(ret)),
            },
            DemandSignature::Thunk { effect, value } => DemandSignature::Thunk {
                effect: self.apply_effect(effect),
                value: Box::new(self.apply_signature(value)),
            },
        }
    }

    pub fn apply_core_type(&self, ty: &DemandCoreType) -> DemandCoreType {
        match ty {
            DemandCoreType::Hole(id) => self
                .cores
                .get(id)
                .map(|ty| self.apply_core_type(ty))
                .unwrap_or(DemandCoreType::Hole(*id)),
            DemandCoreType::Named { path, args } => DemandCoreType::Named {
                path: path.clone(),
                args: args.iter().map(|arg| self.apply_type_arg(arg)).collect(),
            },
            DemandCoreType::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => DemandCoreType::Fun {
                param: Box::new(self.apply_core_type(param)),
                param_effect: Box::new(self.apply_effect(param_effect)),
                ret_effect: Box::new(self.apply_effect(ret_effect)),
                ret: Box::new(self.apply_core_type(ret)),
            },
            DemandCoreType::Tuple(items) => DemandCoreType::Tuple(
                items
                    .iter()
                    .map(|item| self.apply_core_type(item))
                    .collect(),
            ),
            DemandCoreType::Record(fields) => DemandCoreType::Record(
                fields
                    .iter()
                    .map(|field| DemandRecordField {
                        name: field.name.clone(),
                        value: self.apply_core_type(&field.value),
                        optional: field.optional,
                    })
                    .collect(),
            ),
            DemandCoreType::Variant(cases) => DemandCoreType::Variant(
                cases
                    .iter()
                    .map(|case| DemandVariantCase {
                        name: case.name.clone(),
                        payloads: case
                            .payloads
                            .iter()
                            .map(|payload| self.apply_core_type(payload))
                            .collect(),
                    })
                    .collect(),
            ),
            DemandCoreType::RowAsValue(items) => DemandCoreType::RowAsValue(
                items.iter().map(|item| self.apply_effect(item)).collect(),
            ),
            DemandCoreType::Union(items) => DemandCoreType::Union(
                items
                    .iter()
                    .map(|item| self.apply_core_type(item))
                    .collect(),
            ),
            DemandCoreType::Inter(items) => DemandCoreType::Inter(
                items
                    .iter()
                    .map(|item| self.apply_core_type(item))
                    .collect(),
            ),
            DemandCoreType::Recursive { var, body } => DemandCoreType::Recursive {
                var: var.clone(),
                body: Box::new(self.apply_core_type(body)),
            },
            DemandCoreType::Never => DemandCoreType::Never,
        }
    }

    pub fn apply_effect(&self, effect: &DemandEffect) -> DemandEffect {
        match effect {
            DemandEffect::Hole(id) => self
                .effects
                .get(id)
                .map(|effect| self.apply_effect(effect))
                .unwrap_or(DemandEffect::Hole(*id)),
            DemandEffect::Atom(ty) => DemandEffect::Atom(self.apply_core_type(ty)),
            DemandEffect::Row(items) => {
                DemandEffect::Row(items.iter().map(|item| self.apply_effect(item)).collect())
            }
            DemandEffect::Empty => DemandEffect::Empty,
        }
    }

    fn apply_type_arg(&self, arg: &DemandTypeArg) -> DemandTypeArg {
        match arg {
            DemandTypeArg::Type(ty) => DemandTypeArg::Type(self.apply_core_type(ty)),
            DemandTypeArg::Bounds { lower, upper } => DemandTypeArg::Bounds {
                lower: lower.as_ref().map(|ty| self.apply_core_type(ty)),
                upper: upper.as_ref().map(|ty| self.apply_core_type(ty)),
            },
        }
    }
}

#[derive(Debug, Default)]
pub struct DemandUnifier {
    substitutions: DemandSubstitution,
}

impl DemandUnifier {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn unify_signature(
        mut self,
        expected: &DemandSignature,
        actual: &DemandSignature,
    ) -> Result<DemandSubstitution, DemandUnifyError> {
        self.unify(expected, actual)?;
        Ok(self.substitutions)
    }

    pub fn unify(
        &mut self,
        expected: &DemandSignature,
        actual: &DemandSignature,
    ) -> Result<(), DemandUnifyError> {
        self.signature(expected, actual)
    }

    pub fn finish(self) -> DemandSubstitution {
        self.substitutions
    }

    fn signature(
        &mut self,
        expected: &DemandSignature,
        actual: &DemandSignature,
    ) -> Result<(), DemandUnifyError> {
        match (expected, actual) {
            (DemandSignature::Hole(id), actual) => self.bind_value(*id, actual.clone()),
            (expected, DemandSignature::Hole(id)) => self.bind_value(*id, expected.clone()),
            (DemandSignature::Core(expected), DemandSignature::Core(actual)) => {
                self.core(expected, actual)
            }
            (
                DemandSignature::Fun {
                    param: expected_param,
                    ret: expected_ret,
                },
                DemandSignature::Fun {
                    param: actual_param,
                    ret: actual_ret,
                },
            ) => {
                self.signature(expected_param, actual_param)?;
                self.signature(expected_ret, actual_ret)
            }
            (
                DemandSignature::Thunk {
                    effect: expected_effect,
                    value: expected_value,
                },
                DemandSignature::Thunk {
                    effect: actual_effect,
                    value: actual_value,
                },
            ) => {
                self.effect(expected_effect, actual_effect)?;
                self.signature(expected_value, actual_value)
            }
            _ => Err(DemandUnifyError::SignatureMismatch {
                expected: expected.clone(),
                actual: actual.clone(),
            }),
        }
    }

    fn core(
        &mut self,
        expected: &DemandCoreType,
        actual: &DemandCoreType,
    ) -> Result<(), DemandUnifyError> {
        match (expected, actual) {
            (DemandCoreType::Hole(id), actual) => self.bind_core(*id, actual.clone()),
            (expected, DemandCoreType::Hole(id)) => self.bind_core(*id, expected.clone()),
            (DemandCoreType::Never, DemandCoreType::Never) => Ok(()),
            (
                DemandCoreType::Named {
                    path: expected_path,
                    args: expected_args,
                },
                DemandCoreType::Named {
                    path: actual_path,
                    args: actual_args,
                },
            ) if expected_path == actual_path && expected_args.len() == actual_args.len() => {
                for (expected, actual) in expected_args.iter().zip(actual_args) {
                    self.type_arg(expected, actual)?;
                }
                Ok(())
            }
            (
                DemandCoreType::Fun {
                    param: expected_param,
                    param_effect: expected_param_effect,
                    ret_effect: expected_ret_effect,
                    ret: expected_ret,
                },
                DemandCoreType::Fun {
                    param: actual_param,
                    param_effect: actual_param_effect,
                    ret_effect: actual_ret_effect,
                    ret: actual_ret,
                },
            ) => {
                self.core(expected_param, actual_param)?;
                self.effect(expected_param_effect, actual_param_effect)?;
                self.effect(expected_ret_effect, actual_ret_effect)?;
                self.core(expected_ret, actual_ret)
            }
            (DemandCoreType::Tuple(expected), DemandCoreType::Tuple(actual))
            | (DemandCoreType::Union(expected), DemandCoreType::Union(actual))
            | (DemandCoreType::Inter(expected), DemandCoreType::Inter(actual))
                if expected.len() == actual.len() =>
            {
                for (expected, actual) in expected.iter().zip(actual) {
                    self.core(expected, actual)?;
                }
                Ok(())
            }
            (DemandCoreType::RowAsValue(expected), DemandCoreType::RowAsValue(actual))
                if expected.len() == actual.len() =>
            {
                for (expected, actual) in expected.iter().zip(actual) {
                    self.effect(expected, actual)?;
                }
                Ok(())
            }
            _ => Err(DemandUnifyError::CoreMismatch {
                expected: expected.clone(),
                actual: actual.clone(),
            }),
        }
    }

    fn effect(
        &mut self,
        expected: &DemandEffect,
        actual: &DemandEffect,
    ) -> Result<(), DemandUnifyError> {
        match (expected, actual) {
            (DemandEffect::Hole(id), actual) => self.bind_effect(*id, actual.clone()),
            (expected, DemandEffect::Hole(id)) => self.bind_effect(*id, expected.clone()),
            (DemandEffect::Empty, DemandEffect::Empty) => Ok(()),
            (DemandEffect::Atom(expected), DemandEffect::Atom(actual)) => {
                self.core(expected, actual)
            }
            (DemandEffect::Row(expected), DemandEffect::Row(actual))
                if expected.len() == actual.len() =>
            {
                for (expected, actual) in expected.iter().zip(actual) {
                    self.effect(expected, actual)?;
                }
                Ok(())
            }
            _ => Err(DemandUnifyError::EffectMismatch {
                expected: expected.clone(),
                actual: actual.clone(),
            }),
        }
    }

    fn type_arg(
        &mut self,
        expected: &DemandTypeArg,
        actual: &DemandTypeArg,
    ) -> Result<(), DemandUnifyError> {
        match (expected, actual) {
            (DemandTypeArg::Type(expected), DemandTypeArg::Type(actual)) => {
                self.core(expected, actual)
            }
            (
                DemandTypeArg::Bounds {
                    lower: expected_lower,
                    upper: expected_upper,
                },
                DemandTypeArg::Bounds {
                    lower: actual_lower,
                    upper: actual_upper,
                },
            ) => {
                self.optional_core(expected_lower.as_ref(), actual_lower.as_ref())?;
                self.optional_core(expected_upper.as_ref(), actual_upper.as_ref())
            }
            _ => Err(DemandUnifyError::TypeArgMismatch {
                expected: expected.clone(),
                actual: actual.clone(),
            }),
        }
    }

    fn optional_core(
        &mut self,
        expected: Option<&DemandCoreType>,
        actual: Option<&DemandCoreType>,
    ) -> Result<(), DemandUnifyError> {
        match (expected, actual) {
            (Some(expected), Some(actual)) => self.core(expected, actual),
            (None, None) => Ok(()),
            _ => Err(DemandUnifyError::OptionalBoundMismatch),
        }
    }

    fn bind_value(&mut self, id: u32, actual: DemandSignature) -> Result<(), DemandUnifyError> {
        if let Some(existing) = self.substitutions.values.get(&id).cloned() {
            return self.signature(&existing, &actual);
        }
        self.substitutions.values.insert(id, actual);
        Ok(())
    }

    fn bind_core(&mut self, id: u32, actual: DemandCoreType) -> Result<(), DemandUnifyError> {
        if let Some(existing) = self.substitutions.cores.get(&id).cloned() {
            return self.core(&existing, &actual);
        }
        self.substitutions.cores.insert(id, actual);
        Ok(())
    }

    fn bind_effect(&mut self, id: u32, actual: DemandEffect) -> Result<(), DemandUnifyError> {
        if let Some(existing) = self.substitutions.effects.get(&id).cloned() {
            return self.effect(&existing, &actual);
        }
        self.substitutions.effects.insert(id, actual);
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DemandUnifyError {
    SignatureMismatch {
        expected: DemandSignature,
        actual: DemandSignature,
    },
    CoreMismatch {
        expected: DemandCoreType,
        actual: DemandCoreType,
    },
    EffectMismatch {
        expected: DemandEffect,
        actual: DemandEffect,
    },
    TypeArgMismatch {
        expected: DemandTypeArg,
        actual: DemandTypeArg,
    },
    OptionalBoundMismatch,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unifier_solves_value_holes_from_function_demand() {
        let expected = DemandSignature::Fun {
            param: Box::new(DemandSignature::Hole(0)),
            ret: Box::new(DemandSignature::Hole(1)),
        };
        let actual = DemandSignature::Fun {
            param: Box::new(DemandSignature::Core(named("int"))),
            ret: Box::new(DemandSignature::Core(named("int"))),
        };

        let substitutions = DemandUnifier::new()
            .unify_signature(&expected, &actual)
            .expect("unified demand");

        assert_eq!(
            substitutions.values.get(&0),
            Some(&DemandSignature::Core(named("int")))
        );
        assert_eq!(
            substitutions.values.get(&1),
            Some(&DemandSignature::Core(named("int")))
        );
    }

    #[test]
    fn unifier_keeps_effect_holes_in_effect_substitution() {
        let expected = DemandSignature::Thunk {
            effect: DemandEffect::Hole(0),
            value: Box::new(DemandSignature::Core(named("unit"))),
        };
        let actual = DemandSignature::Thunk {
            effect: DemandEffect::Atom(named("io")),
            value: Box::new(DemandSignature::Core(named("unit"))),
        };

        let substitutions = DemandUnifier::new()
            .unify_signature(&expected, &actual)
            .expect("unified demand");

        assert_eq!(
            substitutions.effects.get(&0),
            Some(&DemandEffect::Atom(named("io")))
        );
        assert!(substitutions.values.is_empty());
    }

    fn named(name: &str) -> DemandCoreType {
        DemandCoreType::Named {
            path: core_ir::Path::from_name(core_ir::Name(name.to_string())),
            args: Vec::new(),
        }
    }
}
