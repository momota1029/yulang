//! Default-off symbolic OSig-Demand / OC-CallEff slice. These terms are not
//! original semantic witnesses and have no solver or production consumer.

use crate::shadow::{BinderId, ExprId, Form, PositionId, ShadowArtifact, Skeleton, UseId};

/// Every bridge below remains unresolved, including on successful generation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnresolvedPremise {
    OriginalBX,
    OriginalXi,
    OriginalTypes,
    OriginalScopes,
    EmittedGenCall0Membership,
    CompleteEmittedOriginalCallClauseAndJointWitness,
    InitialSourceDescriptorRelation,
    FiniteSourceBaseEmissionConformanceCertificate,
    CompleteInvocationInterpretation,
    LegalOldWholeTupleSubstitution,
}

const UNRESOLVED: [UnresolvedPremise; 10] = [
    UnresolvedPremise::OriginalBX,
    UnresolvedPremise::OriginalXi,
    UnresolvedPremise::OriginalTypes,
    UnresolvedPremise::OriginalScopes,
    UnresolvedPremise::EmittedGenCall0Membership,
    UnresolvedPremise::CompleteEmittedOriginalCallClauseAndJointWitness,
    UnresolvedPremise::InitialSourceDescriptorRelation,
    UnresolvedPremise::FiniteSourceBaseEmissionConformanceCertificate,
    UnresolvedPremise::CompleteInvocationInterpretation,
    UnresolvedPremise::LegalOldWholeTupleSubstitution,
];

const SOURCE_BASE_UNRESOLVED: [UnresolvedPremise; 4] = [
    UnresolvedPremise::CompleteEmittedOriginalCallClauseAndJointWitness,
    UnresolvedPremise::InitialSourceDescriptorRelation,
    UnresolvedPremise::FiniteSourceBaseEmissionConformanceCertificate,
    UnresolvedPremise::CompleteInvocationInterpretation,
];

/// Pending source-base premises over one retained HIR Apply and its exact root.
/// The inventory entry borrows HIR identities and errors; it grants no call
/// admission, typing, or emitted Gen-Call-0 membership.
#[derive(Debug)]
pub struct PendingResolvedSourceCallStub<'a> {
    root: &'a yu_hir::DefinitionRootId,
    call: yu_hir::shadow::ResolvedCallOccurrence<'a>,
}

impl<'a> PendingResolvedSourceCallStub<'a> {
    pub fn root(&self) -> &'a yu_hir::DefinitionRootId {
        self.root
    }

    pub fn call(&self) -> &yu_hir::shadow::ResolvedCallOccurrence<'a> {
        &self.call
    }

    pub fn unresolved_premises(&self) -> &'static [UnresolvedPremise] {
        &SOURCE_BASE_UNRESOLVED
    }
}

/// Transports the owning HIR inventory without reconstructing source calls.
/// Invalid roots/projections retain the inventory's fail-closed error. This
/// default-off bookkeeping has no production or hot-path consumer; removing it
/// removes only the carrier, without changing compiler behavior.
pub fn generate_resolved_source_calls<'a>(
    module: &'a yu_hir::HirModule,
    root: &'a yu_hir::DefinitionRootId,
) -> Result<Vec<PendingResolvedSourceCallStub<'a>>, yu_hir::shadow::ResolvedCallInventoryError> {
    Ok(module
        .shadow_resolved_call_inventory(root)?
        .into_iter()
        .map(|call| PendingResolvedSourceCallStub { root, call })
        .collect())
}

/// Partial, default-off source identity retention for a direct-Use Apply.
/// Clones preserve artifact brands; they supply no typing or semantic evidence.
/// This shadow-owned stub has no production or hot-path consumer.
#[derive(Debug)]
pub struct PendingSourceCallStub {
    call: ExprId,
    callee_use: UseId,
    argument: ExprId,
    argument_use: Option<UseId>,
}

impl PendingSourceCallStub {
    pub fn call(&self) -> &ExprId {
        &self.call
    }

    pub fn callee_use(&self) -> &UseId {
        &self.callee_use
    }

    pub fn argument(&self) -> &ExprId {
        &self.argument
    }

    pub fn argument_use(&self) -> Option<&UseId> {
        self.argument_use.as_ref()
    }

    pub fn unresolved_premises(&self) -> &'static [UnresolvedPremise] {
        &SOURCE_BASE_UNRESOLVED
    }
}

/// Retains direct-Use Apply identities from one exact retained declaration.
/// Annotations beneath that declaration fail closed. Grouped/computed callees
/// are not inferred through. Empty output establishes neither completeness nor
/// semantic absence.
/// Removing this generator removes only bookkeeping, not compiler behavior.
pub fn generate_source_calls(
    artifact: &ShadowArtifact,
    declaration: &PositionId,
) -> Option<Vec<PendingSourceCallStub>> {
    if declaration_has_annotations(artifact, declaration)? {
        return None;
    }
    let skeleton = artifact.declaration_skeleton(declaration).ok()?;
    skeleton
        .source_call_use_inputs()
        .map(|input| {
            let argument_use = match skeleton.expression(input.argument()).ok()?.form() {
                Form::Use { occurrence, .. } => Some(occurrence.clone()),
                _ => None,
            };
            Some(PendingSourceCallStub {
                call: input.application().expression().clone(),
                callee_use: input.occurrence().clone(),
                argument: input.argument().clone(),
                argument_use,
            })
        })
        .collect()
}

/// Annotation rejection follows the selected source boundary. An annotation
/// in a sibling declaration does not change this declaration's inventory.
/// Errors fail closed; an empty inventory grants no semantic permission.
fn declaration_has_annotations(
    artifact: &ShadowArtifact,
    declaration: &PositionId,
) -> Option<bool> {
    Some(
        !crate::shadow_annotation_boundaries::annotation_boundaries(artifact, declaration)
            .ok()?
            .is_empty(),
    )
}

/// Pending source-generation output, borrowing exact operands without evidence.
/// The shadow generator owns this stub; it has no production or hot-path consumer.
/// Unsupported projections still return None. Removing this carrier rolls back
/// only bookkeeping; it cannot supply a witness or authorize a comparison.
#[derive(Debug)]
pub struct PendingSourceBaseStub<'a> {
    call: &'a ExprId,
    callee_use: &'a UseId,
    argument_use: &'a UseId,
}

impl<'a> PendingSourceBaseStub<'a> {
    pub fn call(&self) -> &'a ExprId {
        self.call
    }

    pub fn callee_use(&self) -> &'a UseId {
        self.callee_use
    }

    pub fn argument_use(&self) -> &'a UseId {
        self.argument_use
    }

    pub fn unresolved_premises(&self) -> &'static [UnresolvedPremise] {
        &SOURCE_BASE_UNRESOLVED
    }
}

/// Tagged construction terms, never numeric semantic identities or type casts.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Address<'a> {
    CalleeUse(&'a UseId),
    UpperChecking(&'a ExprId),
    SourceCallEffect(&'a BinderId),
    InvocationOutput(&'a ExprId),
}

/// One shared formal registration; capture imports this registration unchanged.
#[derive(Debug)]
pub struct SymbolicRegistration<'a> {
    pub declaration: &'a BinderId,
    pub outer_scope: &'a ExprId,
}

/// A local complete Function variable term, not descriptor membership.
#[derive(Debug)]
pub struct SymbolicDemand<'a> {
    pub registration: SymbolicRegistration<'a>,
    pub local_scope: &'a ExprId,
    pub argument_declaration: &'a BinderId,
    pub call: &'a ExprId,
}

/// Source-built singleton record. Private construction prevents supplied inventories.
#[derive(Debug)]
pub struct SymbolicGenCall0<'a> {
    demand: SymbolicDemand<'a>,
    source_base_stub: PendingSourceBaseStub<'a>,
    callee_use: &'a UseId,
    argument_use: &'a UseId,
    returned_use: &'a UseId,
}

impl<'a> SymbolicGenCall0<'a> {
    pub fn source_base_stub(&self) -> &PendingSourceBaseStub<'a> {
        &self.source_base_stub
    }

    pub fn demand(&self) -> &SymbolicDemand<'a> {
        &self.demand
    }

    pub fn callee_use(&self) -> Address<'a> {
        Address::CalleeUse(self.callee_use)
    }

    pub fn argument_use(&self) -> &'a UseId {
        self.argument_use
    }

    pub fn returned_use(&self) -> &'a UseId {
        self.returned_use
    }

    pub fn upper_checking(&self) -> Address<'a> {
        Address::UpperChecking(self.demand.call)
    }

    pub fn source_position(&self) -> Address<'a> {
        Address::SourceCallEffect(self.demand.registration.declaration)
    }

    pub fn invocation_output(&self) -> Address<'a> {
        Address::InvocationOutput(self.demand.call)
    }

    pub fn unresolved_premises(&self) -> &'static [UnresolvedPremise] {
        &UNRESOLVED
    }

    /// Symbolic OSig-Demand reads only the retained demand, never source p0.
    pub fn signature_root(&self) -> SymbolicInvocationRoot<'_, 'a> {
        SymbolicInvocationRoot {
            demand: &self.demand,
        }
    }

    /// Symbolic OC-CallEff retains the complete source record and exact root.
    pub fn call_effect(&self) -> SymbolicCallEffect<'_, 'a> {
        SymbolicCallEffect {
            record: self,
            root: self.signature_root(),
        }
    }
}

/// Inv(Id(U),U) at the same local dependent fiber; no Run/body/latent case.
#[derive(Debug)]
pub struct SymbolicInvocationRoot<'record, 'artifact> {
    demand: &'record SymbolicDemand<'artifact>,
}

#[derive(Debug)]
pub struct SymbolicCallEffect<'record, 'artifact> {
    record: &'record SymbolicGenCall0<'artifact>,
    root: SymbolicInvocationRoot<'record, 'artifact>,
}

/// Only the established unannotated captured singleton topology is projected.
/// Successful lexical checks supply no original typing or emitted membership.
/// Returning the local closure retains this record without adding an invocation.
pub fn generate_captured_singleton(artifact: &ShadowArtifact) -> Option<[SymbolicGenCall0<'_>; 1]> {
    if !artifact.annotations().is_empty() {
        return None;
    }
    let skeleton = artifact.skeleton().ok()?;
    generate_captured_from_skeleton(skeleton)
}

/// Projects the captured singleton from one exact retained direct declaration.
/// Foreign positions and unsupported declaration projections produce no record.
pub fn generate_captured_declaration<'a>(
    artifact: &'a ShadowArtifact,
    declaration: &PositionId,
) -> Option<[SymbolicGenCall0<'a>; 1]> {
    if declaration_has_annotations(artifact, declaration)? {
        return None;
    }
    let skeleton = artifact.declaration_skeleton(declaration).ok()?;
    generate_captured_from_skeleton(skeleton)
}

fn generate_captured_from_skeleton(skeleton: &Skeleton) -> Option<[SymbolicGenCall0<'_>; 1]> {
    let input = skeleton.captured_call_input()?;
    let Form::Lambda {
        parameter,
        body: call,
        ..
    } = skeleton.expression(input.local_lambda()).ok()?.form()
    else {
        return None;
    };
    let Form::Apply { argument, .. } = skeleton.expression(call).ok()?.form() else {
        return None;
    };
    let Form::Use {
        occurrence: argument_use,
        ..
    } = skeleton.expression(argument).ok()?.form()
    else {
        return None;
    };
    // Reborrow from the skeleton: all returned indices belong to the artifact,
    // never to a temporary topology locator or a caller's assumption packet.
    let Form::Apply { callee, .. } = skeleton.expression(call).ok()?.form() else {
        return None;
    };
    let Form::Use {
        binder,
        occurrence: callee_use,
    } = skeleton.expression(callee).ok()?.form()
    else {
        return None;
    };
    let Form::Lambda { body, .. } = skeleton.expression(skeleton.body()).ok()?.form() else {
        return None;
    };
    let Form::Bind {
        value: local_lambda,
        body: returned,
        ..
    } = skeleton.expression(body).ok()?.form()
    else {
        return None;
    };
    let Form::Use {
        occurrence: returned_use,
        ..
    } = skeleton.expression(returned).ok()?.form()
    else {
        return None;
    };
    Some([SymbolicGenCall0 {
        source_base_stub: PendingSourceBaseStub {
            call,
            callee_use,
            argument_use,
        },
        demand: SymbolicDemand {
            registration: SymbolicRegistration {
                declaration: binder,
                outer_scope: skeleton.body(),
            },
            local_scope: local_lambda,
            argument_declaration: parameter,
            call,
        },
        callee_use,
        argument_use,
        returned_use,
    }])
}

impl<'record, 'artifact> SymbolicInvocationRoot<'record, 'artifact> {
    pub fn demand(&self) -> &'record SymbolicDemand<'artifact> {
        self.demand
    }
}

impl<'record, 'artifact> SymbolicCallEffect<'record, 'artifact> {
    pub fn record(&self) -> &'record SymbolicGenCall0<'artifact> {
        self.record
    }
    pub fn root(&self) -> &SymbolicInvocationRoot<'record, 'artifact> {
        &self.root
    }
}
