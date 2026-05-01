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
            (_, DemandCoreType::Never) => Ok(()),
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
            (DemandCoreType::Record(expected), DemandCoreType::Record(actual)) => {
                self.record(expected, actual)
            }
            (DemandCoreType::Variant(expected), DemandCoreType::Variant(actual)) => {
                self.variant(expected, actual)
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

    fn record(
        &mut self,
        expected: &[DemandRecordField],
        actual: &[DemandRecordField],
    ) -> Result<(), DemandUnifyError> {
        if expected.len() != actual.len() {
            return Err(DemandUnifyError::CoreMismatch {
                expected: DemandCoreType::Record(expected.to_vec()),
                actual: DemandCoreType::Record(actual.to_vec()),
            });
        }
        for expected_field in expected {
            let Some(actual_field) = actual.iter().find(|field| {
                field.name == expected_field.name && field.optional == expected_field.optional
            }) else {
                return Err(DemandUnifyError::CoreMismatch {
                    expected: DemandCoreType::Record(expected.to_vec()),
                    actual: DemandCoreType::Record(actual.to_vec()),
                });
            };
            self.core(&expected_field.value, &actual_field.value)?;
        }
        Ok(())
    }

    fn variant(
        &mut self,
        expected: &[DemandVariantCase],
        actual: &[DemandVariantCase],
    ) -> Result<(), DemandUnifyError> {
        if expected.len() != actual.len() {
            return Err(DemandUnifyError::CoreMismatch {
                expected: DemandCoreType::Variant(expected.to_vec()),
                actual: DemandCoreType::Variant(actual.to_vec()),
            });
        }
        for expected_case in expected {
            let Some(actual_case) = actual.iter().find(|case| {
                case.name == expected_case.name
                    && case.payloads.len() == expected_case.payloads.len()
            }) else {
                return Err(DemandUnifyError::CoreMismatch {
                    expected: DemandCoreType::Variant(expected.to_vec()),
                    actual: DemandCoreType::Variant(actual.to_vec()),
                });
            };
            for (expected, actual) in expected_case.payloads.iter().zip(&actual_case.payloads) {
                self.core(expected, actual)?;
            }
        }
        Ok(())
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
            (DemandEffect::Row(expected), DemandEffect::Row(actual)) => {
                self.effect_row(expected, actual)
            }
            (DemandEffect::Row(expected), actual) => {
                self.effect_row(expected, std::slice::from_ref(actual))
            }
            (expected, DemandEffect::Row(actual)) => {
                self.effect_row(std::slice::from_ref(expected), actual)
            }
            _ => Err(DemandUnifyError::EffectMismatch {
                expected: expected.clone(),
                actual: actual.clone(),
            }),
        }
    }

    fn effect_row(
        &mut self,
        expected: &[DemandEffect],
        actual: &[DemandEffect],
    ) -> Result<(), DemandUnifyError> {
        let expected = flatten_effect_row(expected);
        let actual = flatten_effect_row(actual);
        let mut expected_holes = Vec::new();
        let mut expected_fixed = Vec::new();
        let mut actual_holes = Vec::new();
        let mut actual_fixed = Vec::new();
        split_effect_row(expected.clone(), &mut expected_holes, &mut expected_fixed);
        split_effect_row(actual.clone(), &mut actual_holes, &mut actual_fixed);
        remove_shared_effect_holes(&mut expected_holes, &mut actual_holes);

        let mut unmatched_expected = Vec::new();
        for expected in expected_fixed {
            if let Some(index) = self.find_unifiable_effect(&expected, &actual_fixed) {
                actual_fixed.remove(index);
            } else {
                unmatched_expected.push(expected);
            }
        }

        if !unmatched_expected.is_empty() {
            let Some(hole) = actual_holes.pop() else {
                return Err(DemandUnifyError::EffectMismatch {
                    expected: DemandEffect::Row(expected),
                    actual: DemandEffect::Row(actual),
                });
            };
            self.bind_effect(hole, effect_from_row_items(unmatched_expected))?;
        }

        if !actual_fixed.is_empty() {
            let Some(hole) = expected_holes.pop() else {
                return Err(DemandUnifyError::EffectMismatch {
                    expected: DemandEffect::Row(expected),
                    actual: DemandEffect::Row(actual),
                });
            };
            self.bind_effect(hole, effect_from_row_items(actual_fixed))?;
        }

        for hole in expected_holes {
            self.bind_effect(hole, DemandEffect::Empty)?;
        }
        for hole in actual_holes {
            self.bind_effect(hole, DemandEffect::Empty)?;
        }
        Ok(())
    }

    fn find_unifiable_effect(
        &mut self,
        expected: &DemandEffect,
        actual: &[DemandEffect],
    ) -> Option<usize> {
        for (index, candidate) in actual.iter().enumerate() {
            let snapshot = self.substitutions.clone();
            if self.effect(expected, candidate).is_ok() {
                return Some(index);
            }
            self.substitutions = snapshot;
        }
        None
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
        let actual = self.substitutions.apply_signature(&actual);
        if actual == DemandSignature::Hole(id) {
            return Ok(());
        }
        if signature_contains_value_hole(&actual, id) {
            return Err(DemandUnifyError::Occurs {
                namespace: DemandHoleNamespace::Value,
                id,
            });
        }
        if let Some(existing) = self.substitutions.values.get(&id).cloned() {
            return self.signature(&existing, &actual);
        }
        self.substitutions.values.insert(id, actual);
        Ok(())
    }

    fn bind_core(&mut self, id: u32, actual: DemandCoreType) -> Result<(), DemandUnifyError> {
        let actual = self.substitutions.apply_core_type(&actual);
        if actual == DemandCoreType::Hole(id) {
            return Ok(());
        }
        if core_contains_core_hole(&actual, id) {
            return Err(DemandUnifyError::Occurs {
                namespace: DemandHoleNamespace::Core,
                id,
            });
        }
        if let Some(existing) = self.substitutions.cores.get(&id).cloned() {
            return self.core(&existing, &actual);
        }
        self.substitutions.cores.insert(id, actual);
        Ok(())
    }

    fn bind_effect(&mut self, id: u32, actual: DemandEffect) -> Result<(), DemandUnifyError> {
        let actual = self.substitutions.apply_effect(&actual);
        if actual == DemandEffect::Hole(id) {
            return Ok(());
        }
        if effect_contains_effect_hole(&actual, id) {
            return Err(DemandUnifyError::Occurs {
                namespace: DemandHoleNamespace::Effect,
                id,
            });
        }
        if let Some(existing) = self.substitutions.effects.get(&id).cloned() {
            return self.effect(&existing, &actual);
        }
        self.substitutions.effects.insert(id, actual);
        Ok(())
    }
}

fn flatten_effect_row(items: &[DemandEffect]) -> Vec<DemandEffect> {
    let mut out = Vec::new();
    for item in items {
        push_flat_effect(item, &mut out);
    }
    out
}

fn push_flat_effect(effect: &DemandEffect, out: &mut Vec<DemandEffect>) {
    match effect {
        DemandEffect::Empty => {}
        DemandEffect::Row(items) => {
            for item in items {
                push_flat_effect(item, out);
            }
        }
        effect => out.push(effect.clone()),
    }
}

fn split_effect_row(items: Vec<DemandEffect>, holes: &mut Vec<u32>, fixed: &mut Vec<DemandEffect>) {
    for item in items {
        match item {
            DemandEffect::Hole(id) => holes.push(id),
            item => fixed.push(item),
        }
    }
}

fn remove_shared_effect_holes(expected: &mut Vec<u32>, actual: &mut Vec<u32>) {
    expected.retain(|expected_id| {
        if let Some(index) = actual.iter().position(|actual_id| actual_id == expected_id) {
            actual.remove(index);
            false
        } else {
            true
        }
    });
}

fn effect_from_row_items(items: Vec<DemandEffect>) -> DemandEffect {
    match items.as_slice() {
        [] => DemandEffect::Empty,
        [item] => item.clone(),
        _ => DemandEffect::Row(items),
    }
}

fn signature_contains_value_hole(signature: &DemandSignature, id: u32) -> bool {
    match signature {
        DemandSignature::Hole(candidate) => *candidate == id,
        DemandSignature::Core(_) => false,
        DemandSignature::Fun { param, ret } => {
            signature_contains_value_hole(param, id) || signature_contains_value_hole(ret, id)
        }
        DemandSignature::Thunk { value, .. } => signature_contains_value_hole(value, id),
    }
}

fn core_contains_core_hole(ty: &DemandCoreType, id: u32) -> bool {
    match ty {
        DemandCoreType::Never => false,
        DemandCoreType::Hole(candidate) => *candidate == id,
        DemandCoreType::Named { args, .. } => {
            args.iter().any(|arg| type_arg_contains_core_hole(arg, id))
        }
        DemandCoreType::Fun {
            param,
            ret,
            param_effect,
            ret_effect,
        } => {
            core_contains_core_hole(param, id)
                || core_contains_core_hole(ret, id)
                || effect_contains_core_hole(param_effect, id)
                || effect_contains_core_hole(ret_effect, id)
        }
        DemandCoreType::Tuple(items)
        | DemandCoreType::Union(items)
        | DemandCoreType::Inter(items) => {
            items.iter().any(|item| core_contains_core_hole(item, id))
        }
        DemandCoreType::Record(fields) => fields
            .iter()
            .any(|field| core_contains_core_hole(&field.value, id)),
        DemandCoreType::Variant(cases) => cases
            .iter()
            .flat_map(|case| case.payloads.iter())
            .any(|payload| core_contains_core_hole(payload, id)),
        DemandCoreType::RowAsValue(items) => items
            .iter()
            .any(|effect| effect_contains_core_hole(effect, id)),
        DemandCoreType::Recursive { body, .. } => core_contains_core_hole(body, id),
    }
}

fn type_arg_contains_core_hole(arg: &DemandTypeArg, id: u32) -> bool {
    match arg {
        DemandTypeArg::Type(ty) => core_contains_core_hole(ty, id),
        DemandTypeArg::Bounds { lower, upper } => lower
            .iter()
            .chain(upper)
            .any(|ty| core_contains_core_hole(ty, id)),
    }
}

fn effect_contains_core_hole(effect: &DemandEffect, id: u32) -> bool {
    match effect {
        DemandEffect::Empty | DemandEffect::Hole(_) => false,
        DemandEffect::Atom(ty) => core_contains_core_hole(ty, id),
        DemandEffect::Row(items) => items
            .iter()
            .any(|effect| effect_contains_core_hole(effect, id)),
    }
}

fn effect_contains_effect_hole(effect: &DemandEffect, id: u32) -> bool {
    match effect {
        DemandEffect::Empty | DemandEffect::Atom(_) => false,
        DemandEffect::Hole(candidate) => *candidate == id,
        DemandEffect::Row(items) => items
            .iter()
            .any(|effect| effect_contains_effect_hole(effect, id)),
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
    Occurs {
        namespace: DemandHoleNamespace,
        id: u32,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DemandHoleNamespace {
    Value,
    Core,
    Effect,
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

    #[test]
    fn unifier_matches_effect_rows_without_ordering() {
        let expected = DemandSignature::Thunk {
            effect: DemandEffect::Row(vec![
                DemandEffect::Atom(named("io")),
                DemandEffect::Atom(named("undet")),
            ]),
            value: Box::new(DemandSignature::Core(named("unit"))),
        };
        let actual = DemandSignature::Thunk {
            effect: DemandEffect::Row(vec![
                DemandEffect::Atom(named("undet")),
                DemandEffect::Atom(named("io")),
            ]),
            value: Box::new(DemandSignature::Core(named("unit"))),
        };

        DemandUnifier::new()
            .unify_signature(&expected, &actual)
            .expect("unified row order");
    }

    #[test]
    fn unifier_matches_single_effect_atom_with_singleton_row() {
        let expected = DemandSignature::Thunk {
            effect: DemandEffect::Atom(named("io")),
            value: Box::new(DemandSignature::Core(named("unit"))),
        };
        let actual = DemandSignature::Thunk {
            effect: DemandEffect::Row(vec![DemandEffect::Atom(named("io"))]),
            value: Box::new(DemandSignature::Core(named("unit"))),
        };

        DemandUnifier::new()
            .unify_signature(&expected, &actual)
            .expect("unified singleton row");
    }

    #[test]
    fn unifier_solves_effect_hole_inside_row() {
        let expected = DemandSignature::Thunk {
            effect: DemandEffect::Row(vec![DemandEffect::Hole(0), DemandEffect::Atom(named("io"))]),
            value: Box::new(DemandSignature::Core(named("unit"))),
        };
        let actual = DemandSignature::Thunk {
            effect: DemandEffect::Row(vec![
                DemandEffect::Atom(named("undet")),
                DemandEffect::Atom(named("io")),
            ]),
            value: Box::new(DemandSignature::Core(named("unit"))),
        };

        let substitutions = DemandUnifier::new()
            .unify_signature(&expected, &actual)
            .expect("unified row hole");

        assert_eq!(
            substitutions.effects.get(&0),
            Some(&DemandEffect::Atom(named("undet")))
        );
    }

    #[test]
    fn unifier_closes_extra_effect_row_hole_to_empty() {
        let expected = DemandSignature::Thunk {
            effect: DemandEffect::Row(vec![DemandEffect::Atom(named("io")), DemandEffect::Hole(0)]),
            value: Box::new(DemandSignature::Core(named("unit"))),
        };
        let actual = DemandSignature::Thunk {
            effect: DemandEffect::Row(vec![DemandEffect::Atom(named("io"))]),
            value: Box::new(DemandSignature::Core(named("unit"))),
        };

        let substitutions = DemandUnifier::new()
            .unify_signature(&expected, &actual)
            .expect("unified row hole as empty");

        assert_eq!(substitutions.effects.get(&0), Some(&DemandEffect::Empty));
    }

    #[test]
    fn unifier_actual_effect_row_hole_can_absorb_expected_effect() {
        let expected = DemandSignature::Thunk {
            effect: DemandEffect::Row(vec![
                DemandEffect::Atom(named("io")),
                DemandEffect::Atom(named("undet")),
            ]),
            value: Box::new(DemandSignature::Core(named("unit"))),
        };
        let actual = DemandSignature::Thunk {
            effect: DemandEffect::Row(vec![DemandEffect::Atom(named("io")), DemandEffect::Hole(0)]),
            value: Box::new(DemandSignature::Core(named("unit"))),
        };

        let substitutions = DemandUnifier::new()
            .unify_signature(&expected, &actual)
            .expect("unified actual row hole");

        assert_eq!(
            substitutions.effects.get(&0),
            Some(&DemandEffect::Atom(named("undet")))
        );
    }

    #[test]
    fn unifier_accepts_never_as_bottom_core_type() {
        DemandUnifier::new()
            .unify_signature(
                &DemandSignature::Core(named("unit")),
                &DemandSignature::Core(DemandCoreType::Never),
            )
            .expect("never is a bottom value");
    }

    #[test]
    fn unifier_matches_record_fields_by_name() {
        let expected = DemandSignature::Core(DemandCoreType::Record(vec![
            field("x", named("int")),
            field("y", named("bool")),
        ]));
        let actual = DemandSignature::Core(DemandCoreType::Record(vec![
            field("y", named("bool")),
            field("x", named("int")),
        ]));

        DemandUnifier::new()
            .unify_signature(&expected, &actual)
            .expect("record fields unified by name");
    }

    #[test]
    fn unifier_matches_variant_cases_by_name() {
        let expected = DemandSignature::Core(DemandCoreType::Variant(vec![
            case("nil", Vec::new()),
            case("just", vec![named("int")]),
        ]));
        let actual = DemandSignature::Core(DemandCoreType::Variant(vec![
            case("just", vec![named("int")]),
            case("nil", Vec::new()),
        ]));

        DemandUnifier::new()
            .unify_signature(&expected, &actual)
            .expect("variant cases unified by name");
    }

    #[test]
    fn unifier_rejects_recursive_value_hole() {
        let error = DemandUnifier::new()
            .unify_signature(
                &DemandSignature::Hole(0),
                &DemandSignature::Fun {
                    param: Box::new(DemandSignature::Hole(0)),
                    ret: Box::new(DemandSignature::Core(named("int"))),
                },
            )
            .expect_err("recursive value hole");

        assert_eq!(
            error,
            DemandUnifyError::Occurs {
                namespace: DemandHoleNamespace::Value,
                id: 0,
            }
        );
    }

    #[test]
    fn unifier_rejects_recursive_core_hole() {
        let error = DemandUnifier::new()
            .unify_signature(
                &DemandSignature::Core(DemandCoreType::Hole(0)),
                &DemandSignature::Core(DemandCoreType::Tuple(vec![DemandCoreType::Hole(0)])),
            )
            .expect_err("recursive core hole");

        assert_eq!(
            error,
            DemandUnifyError::Occurs {
                namespace: DemandHoleNamespace::Core,
                id: 0,
            }
        );
    }

    #[test]
    fn unifier_rejects_recursive_effect_hole() {
        let error = DemandUnifier::new()
            .unify_signature(
                &DemandSignature::Thunk {
                    effect: DemandEffect::Hole(0),
                    value: Box::new(DemandSignature::Core(named("unit"))),
                },
                &DemandSignature::Thunk {
                    effect: DemandEffect::Row(vec![
                        DemandEffect::Hole(0),
                        DemandEffect::Atom(named("io")),
                    ]),
                    value: Box::new(DemandSignature::Core(named("unit"))),
                },
            )
            .expect_err("recursive effect hole");

        assert_eq!(
            error,
            DemandUnifyError::Occurs {
                namespace: DemandHoleNamespace::Effect,
                id: 0,
            }
        );
    }

    fn named(name: &str) -> DemandCoreType {
        DemandCoreType::Named {
            path: core_ir::Path::from_name(core_ir::Name(name.to_string())),
            args: Vec::new(),
        }
    }

    fn field(name: &str, value: DemandCoreType) -> DemandRecordField {
        DemandRecordField {
            name: core_ir::Name(name.to_string()),
            value,
            optional: false,
        }
    }

    fn case(name: &str, payloads: Vec<DemandCoreType>) -> DemandVariantCase {
        DemandVariantCase {
            name: core_ir::Name(name.to_string()),
            payloads,
        }
    }
}
