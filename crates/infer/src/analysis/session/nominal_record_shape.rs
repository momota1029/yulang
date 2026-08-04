//! Resolve nominal-record bridge obligations against lowering certificates.
//!
//! The constraint machine emits only the canonical producer and endpoints. This module owns the
//! poly metadata and projection-scheme lifecycle, then returns ordinary derived subtypes to the
//! same machine.

use super::*;

use crate::constraints::{NominalRecordShapeObligation, UnsatisfiedSubtypeShapeEvent};

impl AnalysisSession {
    pub(super) fn route_nominal_record_shape_obligation(
        &mut self,
        obligation: NominalRecordShapeObligation,
    ) {
        if !self
            .nominal_record_shape_obligation_keys
            .insert(obligation.producer)
        {
            return;
        }
        self.resolve_or_defer_nominal_record_shape_obligation(obligation);
    }

    pub(super) fn retry_pending_nominal_record_shape_obligations(&mut self) {
        let pending = std::mem::take(&mut self.pending_nominal_record_shape_obligations);
        for obligation in pending {
            self.resolve_or_defer_nominal_record_shape_obligation(obligation);
        }
    }

    pub(crate) fn reject_pending_nominal_record_shape_obligations_at_quiescence(&mut self) {
        let pending = std::mem::take(&mut self.pending_nominal_record_shape_obligations);
        for obligation in pending {
            self.reject_nominal_record_shape_obligation(obligation);
        }
    }

    fn resolve_or_defer_nominal_record_shape_obligation(
        &mut self,
        obligation: NominalRecordShapeObligation,
    ) {
        let (owner_path, required_fields) = {
            let types = self.infer.constraints().types();
            let Pos::Con(owner_path, _) = types.pos(obligation.lower) else {
                self.reject_nominal_record_shape_obligation(obligation);
                return;
            };
            let Neg::Record(required_fields) = types.neg(obligation.upper) else {
                self.reject_nominal_record_shape_obligation(obligation);
                return;
            };
            (owner_path.clone(), required_fields.clone())
        };
        let Some(shape) = self.poly.nominal_record_shapes.get(&owner_path).cloned() else {
            self.reject_nominal_record_shape_obligation(obligation);
            return;
        };

        let mut projections = Vec::with_capacity(required_fields.len());
        for (index, required) in required_fields.iter().enumerate() {
            let Some(field) = shape
                .fields
                .iter()
                .find(|field| field.name == required.name)
            else {
                if required.optional {
                    continue;
                }
                self.reject_nominal_record_shape_obligation(obligation);
                return;
            };
            let Some(Def::Let {
                scheme: Some(scheme),
                ..
            }) = self.poly.defs.get(field.projection)
            else {
                self.pending_nominal_record_shape_obligations
                    .push(obligation);
                return;
            };
            projections.push((index, field.projection, scheme.clone(), required.value));
        }

        let mut derived = Vec::with_capacity(projections.len());
        for (index, projection, scheme, required) in projections {
            let imported = self.imported_scheme_defs.contains(&projection);
            let finalized_template = self.finalized_template_scheme_defs.contains(&projection);
            let instantiated = if imported || finalized_template {
                let empty_boundary = ImportedBoundarySubstitution::default();
                let boundary = if imported {
                    &self.imported_boundary
                } else {
                    &empty_boundary
                };
                if validate_imported_scheme_for_instantiation(&self.poly.typ, &scheme, boundary)
                    .is_err()
                {
                    self.reject_nominal_record_shape_obligation(obligation);
                    return;
                }
                instantiate_validated_imported_scheme_with_roles(
                    &self.poly.typ,
                    &mut self.infer,
                    TypeLevel::secondary(),
                    &scheme,
                    boundary,
                )
            } else {
                instantiate_scheme_with_roles_and_provenance(
                    &self.poly.typ,
                    &mut self.infer,
                    TypeLevel::secondary(),
                    &scheme,
                    &[],
                )
                .0
            };
            let Pos::Fun { arg, ret, .. } = self
                .infer
                .constraints()
                .types()
                .pos(instantiated.predicate)
                .clone()
            else {
                self.reject_nominal_record_shape_obligation(obligation);
                return;
            };
            derived.push((index, arg, ret, required));
        }
        self.infer
            .derive_nominal_record_fields(obligation.producer, derived);
    }

    fn reject_nominal_record_shape_obligation(&mut self, obligation: NominalRecordShapeObligation) {
        let (actual, expected) = {
            let types = self.infer.constraints().types();
            let actual = match types.pos(obligation.lower) {
                Pos::Con(path, _) => ConcreteSubtypeHead::Constructor(path.clone()),
                _ => return,
            };
            let expected = match types.neg(obligation.upper) {
                Neg::Record(fields) => ConcreteSubtypeHead::Record(
                    fields.iter().map(|field| field.name.clone()).collect(),
                ),
                _ => return,
            };
            (actual, expected)
        };
        self.record_unsatisfied_subtype_shape(UnsatisfiedSubtypeShapeEvent {
            actual,
            expected,
            producer: obligation.producer,
        });
    }
}
