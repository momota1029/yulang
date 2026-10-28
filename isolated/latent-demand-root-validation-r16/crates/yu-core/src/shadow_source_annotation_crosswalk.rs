//! Default-off structural HIR/CST crosswalk. No typing or semantic evidence.

use crate::shadow::{Position, PositionId, ShadowArtifact, ShadowError};
use crate::shadow_annotation_boundaries::{
    AnnotationBoundaryError, AnnotationBoundaryOccurrence, annotation_boundaries,
};
use yu_hir::shadow::{ResolvedCallInventoryError, ResolvedCallOccurrence, SourceIdentityError};
use yu_hir::{DefinitionRootId, HirModule};
use yu_syntax::SyntaxKind;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnresolvedPremise {
    AnnotationTypedPortAndProfileCorrespondence,
    AnnotationApplicabilityAndPermission,
    CallTypingAndAdmission,
    SourceCallCompleteness,
    OriginalXi,
    OriginalTypes,
    OriginalScopes,
    OriginalSemanticWitness,
    LegalWholeTupleSubstitution,
}

const UNRESOLVED: [UnresolvedPremise; 9] = [
    UnresolvedPremise::AnnotationTypedPortAndProfileCorrespondence,
    UnresolvedPremise::AnnotationApplicabilityAndPermission,
    UnresolvedPremise::CallTypingAndAdmission,
    UnresolvedPremise::SourceCallCompleteness,
    UnresolvedPremise::OriginalXi,
    UnresolvedPremise::OriginalTypes,
    UnresolvedPremise::OriginalScopes,
    UnresolvedPremise::OriginalSemanticWitness,
    UnresolvedPremise::LegalWholeTupleSubstitution,
];

#[derive(Debug)]
pub struct SourcePosition<'a> {
    pub id: PositionId,
    pub position: &'a Position,
}

/// Existing Apply identities and diagnostic IDs are pending metadata only.
#[derive(Debug)]
pub struct RetainedCall<'a> {
    pub identity: ResolvedCallOccurrence<'a>,
    pub call: SourcePosition<'a>,
    pub callee: SourcePosition<'a>,
    pub argument: SourcePosition<'a>,
}

/// Unsupported projection preserves the independent annotation inventory,
/// without pretending that no calls exist.
#[derive(Debug)]
pub enum CallProjection<'a> {
    Retained(Vec<RetainedCall<'a>>),
    Unsupported(ResolvedCallInventoryError),
}

#[derive(Debug)]
pub struct SourceAnnotationCrosswalk<'a> {
    pub root: &'a DefinitionRootId,
    pub boundary: SourcePosition<'a>,
    /// Complete only over the selected retained HIR traversal, including its
    /// optional cold local initializer. Empty output says nothing about source calls.
    pub calls: CallProjection<'a>,
    /// Complete syntactic inventory beneath the definition, including nested
    /// declarations. No annotation is associated with any individual call.
    pub annotations: Vec<AnnotationBoundaryOccurrence<'a>>,
}

impl SourceAnnotationCrosswalk<'_> {
    pub fn unresolved_premises(&self) -> &'static [UnresolvedPremise] {
        &UNRESOLVED
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CrosswalkError {
    Identity(SourceIdentityError),
    Inventory(ResolvedCallInventoryError),
    Source(ShadowError),
    Annotations(AnnotationBoundaryError),
    UnsupportedStructure,
}

/// Joins exact paired parse identities and checks retained ancestry for every
/// operand. Malformed or unsupported projections fail closed structurally;
/// retained UnsupportedExpression diagnostics do not reject semantic calls.
pub fn source_annotation_crosswalk<'a>(
    module: &'a HirModule,
    root: &'a DefinitionRootId,
    artifact: &'a ShadowArtifact,
) -> Result<SourceAnnotationCrosswalk<'a>, CrosswalkError> {
    let boundary_id = artifact
        .definition_source_position(module, root)
        .map_err(CrosswalkError::Identity)?;
    let boundary_position = artifact
        .position(&boundary_id)
        .map_err(CrosswalkError::Source)?;
    if !boundary_position.is_node() || boundary_position.kind() != SyntaxKind::BindingStatement {
        return Err(CrosswalkError::UnsupportedStructure);
    }
    // Borrow the artifact's exact boundary ID from its retained child's parent,
    // so annotation rows do not borrow a temporary cloned identity.
    let child = boundary_position
        .children()
        .first()
        .ok_or(CrosswalkError::UnsupportedStructure)?;
    let retained_boundary = artifact
        .position(child)
        .map_err(CrosswalkError::Source)?
        .parent()
        .filter(|parent| *parent == &boundary_id)
        .ok_or(CrosswalkError::UnsupportedStructure)?;
    let annotations =
        annotation_boundaries(artifact, retained_boundary).map_err(CrosswalkError::Annotations)?;
    let inventory = match module.shadow_resolved_call_inventory(root) {
        Ok(inventory) => inventory,
        Err(error @ ResolvedCallInventoryError::UnsupportedProjection) => {
            return Ok(SourceAnnotationCrosswalk {
                root,
                boundary: SourcePosition {
                    id: boundary_id,
                    position: boundary_position,
                },
                calls: CallProjection::Unsupported(error),
                annotations,
            });
        }
        Err(error) => return Err(CrosswalkError::Inventory(error)),
    };
    let mut calls = Vec::with_capacity(inventory.len());
    for identity in inventory {
        let resolve = |occurrence| {
            let id = artifact
                .occurrence_source_position(module, occurrence)
                .map_err(CrosswalkError::Identity)?;
            source_under_boundary(artifact, id, &boundary_id)
        };
        let call = resolve(identity.occurrence)?;
        if !call.position.is_node() || call.position.kind() != identity.source_form {
            return Err(CrosswalkError::UnsupportedStructure);
        }
        let callee = resolve(identity.callee)?;
        let argument = resolve(identity.argument)?;
        calls.push(RetainedCall {
            identity,
            call,
            callee,
            argument,
        });
    }
    Ok(SourceAnnotationCrosswalk {
        root,
        boundary: SourcePosition {
            id: boundary_id,
            position: boundary_position,
        },
        calls: CallProjection::Retained(calls),
        annotations,
    })
}

fn source_under_boundary<'a>(
    artifact: &'a ShadowArtifact,
    id: PositionId,
    boundary: &PositionId,
) -> Result<SourcePosition<'a>, CrosswalkError> {
    let position = artifact.position(&id).map_err(CrosswalkError::Source)?;
    if !position.is_node() {
        return Err(CrosswalkError::UnsupportedStructure);
    }
    let mut parent = position.parent();
    // Bound traversal by the retained inventory to fail closed on malformed cycles.
    for _ in 0..artifact.positions().len() {
        let ancestor = parent.ok_or(CrosswalkError::UnsupportedStructure)?;
        let retained = artifact
            .position(ancestor)
            .map_err(CrosswalkError::Source)?;
        if ancestor == boundary {
            return Ok(SourcePosition { id, position });
        }
        parent = retained.parent();
    }
    Err(CrosswalkError::UnsupportedStructure)
}
