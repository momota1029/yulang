//! Default-off syntax annotation inventory for one exact retained declaration.
//! No production consumer, type judgment, annotation permission or call view is supplied.

use crate::shadow::{AnnotationOccurrence, Position, PositionId, ShadowArtifact, ShadowError};
use yu_syntax::SyntaxKind;

/// Borrows an existing occurrence and its caller-selected syntax boundary.
/// Typed-port/profile correspondence remains the occurrence's pending premise;
/// annotation applicability and source-boundary semantics remain unresolved.
#[derive(Debug)]
pub struct AnnotationBoundaryOccurrence<'a> {
    pub boundary: &'a PositionId,
    pub occurrence: &'a AnnotationOccurrence,
    pub position: &'a Position,
}

/// Complete retained syntax inventory beneath one exact BindingStatement.
/// Ownership follows retained parent ancestry, including nested declarations.
/// An empty result describes this inventory only, without semantic absence or
/// permission. Ordering follows source ranges; ranges never assign ownership.
/// This cold, removable observation does not invoke lowering or solving.
pub fn annotation_boundaries<'a>(
    artifact: &'a ShadowArtifact,
    boundary: &'a PositionId,
) -> Result<Vec<AnnotationBoundaryOccurrence<'a>>, AnnotationBoundaryError> {
    let root = artifact.position(boundary)?;
    if !root.is_node() || root.kind() != SyntaxKind::BindingStatement {
        return Err(AnnotationBoundaryError::NonBindingRoot);
    }
    let mut annotations = Vec::new();
    for occurrence in artifact.annotations() {
        let position = artifact.position(occurrence.position())?;
        let mut parent = position.parent();
        while let Some(id) = parent {
            let retained = artifact.position(id)?;
            if id == boundary {
                annotations.push(AnnotationBoundaryOccurrence {
                    boundary,
                    occurrence,
                    position,
                });
                break;
            }
            parent = retained.parent();
        }
    }
    annotations.sort_by_key(|annotation| {
        (
            annotation.position.range().start,
            annotation.position.range().end,
        )
    });
    Ok(annotations)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AnnotationBoundaryError {
    Source(ShadowError),
    NonBindingRoot,
}

impl From<ShadowError> for AnnotationBoundaryError {
    fn from(error: ShadowError) -> Self {
        Self::Source(error)
    }
}
