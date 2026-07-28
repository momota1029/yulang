//! Check nominal owners against structural record requirements.
//!
//! The certificate identifies real struct fields and their projection definitions. The projection
//! scheme remains the source of truth for field types, including generic owner arguments.

use super::*;

impl TypeGraph<'_> {
    pub(super) fn constrain_nominal_record_shape(
        &mut self,
        owner_path: Vec<String>,
        owner_args: Vec<Type>,
        lower_weight: StackWeight,
        required_fields: Vec<TypeField>,
        upper_weight: StackWeight,
        provenance: Option<SpecializeSubtypeProvenanceRecordId>,
    ) -> Result<(), SpecializeError> {
        let owner = Type::Con {
            path: owner_path.clone(),
            args: owner_args,
        };
        let Some(shape) = self.arena.nominal_record_shapes.get(&owner_path).cloned() else {
            return self.reject_nominal_record_shape(owner, required_fields, provenance);
        };

        let mut projections = Vec::with_capacity(required_fields.len());
        for (required_index, required) in required_fields.iter().enumerate() {
            let Some((shape_index, field)) = shape
                .fields
                .iter()
                .enumerate()
                .find(|(_, field)| field.name == required.name)
            else {
                if required.optional {
                    continue;
                }
                return self.reject_nominal_record_shape(owner, required_fields, provenance);
            };
            let Some(poly_expr::Def::Let {
                scheme: Some(scheme),
                ..
            }) = self.arena.defs.get(field.projection)
            else {
                return self.reject_nominal_record_shape(owner, required_fields, provenance);
            };
            projections.push((
                shape_index,
                required_index,
                field.projection,
                scheme.clone(),
                required.value.clone(),
            ));
        }

        for (shape_index, required_index, projection, scheme, required) in projections {
            let instantiated = self.instantiate_scheme(projection, &scheme)?;
            let Type::Fun { arg, ret, .. } = instantiated else {
                return self.reject_nominal_record_shape(owner, required_fields, provenance);
            };
            let lower_step = nominal_record_field_step(shape_index);
            let upper_step = nominal_record_field_step(required_index);
            self.constrain_structural_subtype(
                owner.clone(),
                lower_weight.clone(),
                *arg,
                upper_weight.clone(),
                provenance,
                lower_step,
                upper_step,
            )?;
            self.constrain_structural_subtype(
                *ret,
                lower_weight.clone(),
                required,
                upper_weight.clone(),
                provenance,
                lower_step,
                upper_step,
            )?;
        }
        Ok(())
    }

    fn reject_nominal_record_shape(
        &mut self,
        owner: Type,
        required_fields: Vec<TypeField>,
        provenance: Option<SpecializeSubtypeProvenanceRecordId>,
    ) -> Result<(), SpecializeError> {
        let provenance = self.record_shadow_failure(provenance);
        unsatisfied_subtype(owner, Type::Record(required_fields), provenance)
    }
}

fn nominal_record_field_step(index: usize) -> TypePositionStep {
    TypePositionStep::RecordField {
        alternative: poly::provenance::TypePositionIndex::from_usize(0),
        field: poly::provenance::TypePositionIndex::from_usize(index),
    }
}
