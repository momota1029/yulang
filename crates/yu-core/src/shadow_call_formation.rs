//! Default-off symbolic OSig-Demand / OC-CallEff slice. These terms are not
//! original semantic witnesses and have no solver or production consumer.

use crate::shadow::{BinderId, ExprId, Form, ShadowArtifact, UseId};

/// Every bridge below remains unresolved, including on successful generation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnresolvedPremise {
    OriginalBX,
    OriginalXi,
    OriginalTypes,
    OriginalScopes,
    EmittedGenCall0Membership,
    CompleteInvocationInterpretation,
    LegalOldWholeTupleSubstitution,
}

const UNRESOLVED: [UnresolvedPremise; 7] = [
    UnresolvedPremise::OriginalBX,
    UnresolvedPremise::OriginalXi,
    UnresolvedPremise::OriginalTypes,
    UnresolvedPremise::OriginalScopes,
    UnresolvedPremise::EmittedGenCall0Membership,
    UnresolvedPremise::CompleteInvocationInterpretation,
    UnresolvedPremise::LegalOldWholeTupleSubstitution,
];

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
    callee_use: &'a UseId,
    argument_use: &'a UseId,
    returned_use: &'a UseId,
}

impl<'a> SymbolicGenCall0<'a> {
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
