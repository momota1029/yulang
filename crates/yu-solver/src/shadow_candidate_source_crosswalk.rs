//! Test-wired, default-off observational crosswalk for one root Lambda.
//! Exact source incidence and candidate solver output never discharge premises.
#![cfg(feature = "shadow-apply-candidate")]

use yu_hir::shadow::{
    Form, PendingPremise, ShadowArtifact, Skeleton, SourceCallUseInput, SourceIdentityError,
};
use yu_hir::{DefinitionRootId, HirItem, HirModule, ResolvedExpr};
use yu_solver::shadow_apply::{
    CandidateCall, CandidateExport, CandidateFreshRow, CandidateValueObservation,
};

/// The existing one-binding source skeleton supplies no ordinary incoming-use
/// join. Captured local Bind/Lambda source remains outside the solver envelope.
pub struct CandidateSourceCrosswalk<'a> {
    source: &'a ShadowArtifact,
    skeleton: &'a Skeleton,
    hir: &'a HirModule,
    candidate: &'a CandidateValueObservation,
    source_parameter: &'a yu_hir::shadow::BinderId,
    export: CandidateExport<'a>,
}

#[derive(Debug)]
pub enum CrosswalkError {
    Source(SourceIdentityError),
    MissingExactSourceIncidence,
    ForeignCandidate,
}

/// Borrows the original symbolic carrier and candidate call; neither is rebuilt.
pub struct CandidateSourceCall<'a> {
    input: SourceCallUseInput<'a>,
    candidate: &'a CandidateCall,
    skeleton: &'a Skeleton,
    observation: &'a CandidateValueObservation,
}
impl<'a> CandidateSourceCall<'a> {
    pub fn source_input(&self) -> &SourceCallUseInput<'a> {
        &self.input
    }
    pub fn candidate_call(&self) -> &'a CandidateCall {
        self.candidate
    }
    pub fn pending(&self) -> impl Iterator<Item = &'a PendingPremise> + '_ {
        self.skeleton
            .pending()
            .iter()
            .filter(|premise| premise.call() == self.input.application().expression())
    }
    /// Validated against actual candidate capture: an own formal has no ordinary
    /// incoming substitution. This does not supply a missing fresh-use bridge.
    pub fn ordinary_incoming_rows(&self) -> Option<Vec<CandidateFreshRow<'a>>> {
        self.observation.fresh_rows(&self.candidate.callee)
    }
}
impl<'a> CandidateSourceCrosswalk<'a> {
    pub fn new(
        source: &'a ShadowArtifact,
        hir: &'a HirModule,
        candidate: &'a CandidateValueObservation,
        root: &DefinitionRootId,
    ) -> Result<Self, CrosswalkError> {
        let missing = || CrosswalkError::MissingExactSourceIncidence;
        let skeleton = source.skeleton().map_err(|_| missing())?;
        let [HirItem::Binding(binding)] = hir.items() else {
            return Err(missing());
        };
        if binding.definition_root() != root {
            return Err(missing());
        }
        let ResolvedExpr::Lambda { parameter, .. } = binding.value() else {
            return Err(missing());
        };
        let declaration = source
            .definition_source_position(hir, root)
            .map_err(CrosswalkError::Source)?;
        // Ordinary one-binding skeletons designate the body expression. Their
        // separately retained root Lambda is located by the declaration position.
        let source_crosswalk = source.skeleton_source_crosswalk();
        let (expression, _) = source_crosswalk
            .definition_at_position(&declaration)
            .map_err(|_| missing())?
            .ok_or_else(missing)?;
        let Form::Lambda {
            parameter: source_parameter,
            ..
        } = expression.form()
        else {
            return Err(missing());
        };
        let formal = source
            .parameter_source_position(hir, parameter)
            .map_err(CrosswalkError::Source)?;
        if expression.position() != &declaration
            || skeleton
                .binder(source_parameter)
                .map_err(|_| missing())?
                .position()
                != &formal
        {
            return Err(missing());
        }
        let export = candidate
            .export(root)
            .map_err(|_| CrosswalkError::ForeignCandidate)?;
        let result = Self {
            source,
            skeleton,
            hir,
            candidate,
            source_parameter,
            export,
        };
        // Validate the complete bounded observation before returning a crosswalk.
        for call in candidate.calls() {
            result.call(call)?;
        }
        Ok(result)
    }
    pub fn export(&self) -> &CandidateExport<'a> {
        &self.export
    }
    pub fn calls(&self) -> impl Iterator<Item = CandidateSourceCall<'a>> + '_ {
        self.candidate.calls().iter().map(|call| {
            self.call(call)
                .expect("immutable crosswalk was completely validated")
        })
    }
    fn call(&self, call: &'a CandidateCall) -> Result<CandidateSourceCall<'a>, CrosswalkError> {
        let missing = || CrosswalkError::MissingExactSourceIncidence;
        let position = self
            .source
            .occurrence_source_position(self.hir, &call.occurrence)
            .map_err(CrosswalkError::Source)?;
        let input = self
            .skeleton
            .source_call_use_inputs()
            .find(|input| input.application().position() == &position)
            .ok_or_else(missing)?;
        let callee = self
            .source
            .occurrence_source_position(self.hir, &call.callee)
            .map_err(CrosswalkError::Source)?;
        let argument = self
            .source
            .occurrence_source_position(self.hir, &call.argument)
            .map_err(CrosswalkError::Source)?;
        if input.binder() != self.source_parameter
            || self
                .skeleton
                .use_position(input.occurrence())
                .map_err(|_| missing())?
                != &callee
            || self
                .skeleton
                .expression(input.argument())
                .map_err(|_| missing())?
                .position()
                != &argument
            || self.candidate.fresh_rows(&call.callee).is_some()
        {
            return Err(missing());
        }
        Ok(CandidateSourceCall {
            input,
            candidate: call,
            skeleton: self.skeleton,
            observation: self.candidate,
        })
    }
}
