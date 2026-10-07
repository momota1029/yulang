//! Test-wired, default-off observational crosswalk for independent root Lambdas.
//! Exact source incidence and candidate solver output never discharge premises.
#![cfg(feature = "shadow-apply-candidate")]
#![allow(
    dead_code,
    reason = "test-wired crosswalk APIs are exercised by separate integration targets"
)]

use yu_hir::shadow::{
    Form, PendingPremise, ShadowArtifact, Skeleton, SourceCallUseInput, SourceIdentityError,
};
use yu_hir::{DefinitionRootId, HirItem, HirModule, ResolvedExpr};
use yu_solver::shadow_apply::{
    CandidateCall, CandidateExport, CandidateFreshRow, CandidateValueObservation,
};

/// Validates all observed calls using each exact owning declaration before export.
pub struct CandidateSourceCrosswalk<'a> {
    calls: Vec<CandidateSourceCall<'a>>,
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
        let mut owners = std::collections::HashMap::new();
        let mut selected = false;
        for item in hir.items() {
            let HirItem::Binding(binding) = item else {
                return Err(missing());
            };
            let ResolvedExpr::Lambda { parameter, .. } = binding.value() else {
                return Err(missing());
            };
            let declaration = source
                .definition_source_position(hir, binding.definition_root())
                .map_err(CrosswalkError::Source)?;
            let skeleton = source
                .declaration_skeleton(&declaration)
                .map_err(|_| missing())?;
            let expression = skeleton
                .expressions()
                .iter()
                .find(|expression| expression.position() == &declaration)
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
            if skeleton
                .binder(source_parameter)
                .map_err(|_| missing())?
                .position()
                != &formal
            {
                return Err(missing());
            }
            selected |= binding.definition_root() == root;
            // Ownership follows the retained HIR tree, never IDs, spelling or shape.
            let mut pending = vec![binding.value()];
            while let Some(expression) = pending.pop() {
                if owners
                    .insert(expression.occurrence(), (skeleton, source_parameter))
                    .is_some()
                {
                    return Err(missing());
                }
                match expression {
                    ResolvedExpr::Lambda { body, .. } => pending.push(body),
                    ResolvedExpr::Group { inner, .. } => pending.push(inner),
                    ResolvedExpr::Apply {
                        callee, argument, ..
                    } => {
                        pending.push(callee);
                        pending.push(argument);
                    }
                    _ => {}
                }
            }
        }
        if !selected {
            return Err(missing());
        }
        let export = candidate
            .export(root)
            .map_err(|_| CrosswalkError::ForeignCandidate)?;
        let mut calls = Vec::new();
        for call in candidate.calls() {
            let (skeleton, source_parameter) =
                owners.get(&call.occurrence).copied().ok_or_else(missing)?;
            if owners.get(&call.callee).map(|(_, formal)| *formal) != Some(source_parameter)
                || owners.get(&call.argument).map(|(_, formal)| *formal) != Some(source_parameter)
            {
                return Err(missing());
            }
            let position = source
                .occurrence_source_position(hir, &call.occurrence)
                .map_err(CrosswalkError::Source)?;
            let input = skeleton
                .source_call_use_inputs()
                .find(|input| input.application().position() == &position)
                .ok_or_else(missing)?;
            let callee = source
                .occurrence_source_position(hir, &call.callee)
                .map_err(CrosswalkError::Source)?;
            let argument = source
                .occurrence_source_position(hir, &call.argument)
                .map_err(CrosswalkError::Source)?;
            if input.binder() != source_parameter
                || skeleton
                    .use_position(input.occurrence())
                    .map_err(|_| missing())?
                    != &callee
                || skeleton
                    .expression(input.argument())
                    .map_err(|_| missing())?
                    .position()
                    != &argument
                || candidate.fresh_rows(&call.callee).is_some()
            {
                return Err(missing());
            }
            calls.push(CandidateSourceCall {
                input,
                candidate: call,
                skeleton,
                observation: candidate,
            });
        }
        Ok(Self { calls, export })
    }
    pub fn export(&self) -> &CandidateExport<'a> {
        &self.export
    }
    pub fn calls(&self) -> impl Iterator<Item = CandidateSourceCall<'a>> + '_ {
        self.calls.iter().map(|call| CandidateSourceCall {
            input: call
                .skeleton
                .source_call_use_inputs()
                .find(|input| {
                    input.application().expression() == call.input.application().expression()
                })
                .expect("validated immutable source incidence"),
            candidate: call.candidate,
            skeleton: call.skeleton,
            observation: call.observation,
        })
    }
}

/// Raw module Name positions joined to retained collection uses. This path does
/// not construct a Lambda skeleton or a SourceCallUseInput.
pub struct CandidateSourceModuleUse<'a> {
    position: yu_hir::shadow::PositionId,
    target_position: yu_hir::shadow::PositionId,
    receiving_position: yu_hir::shadow::PositionId,
    observation: yu_solver::shadow_apply::CandidateDefinitionUseRef<'a>,
}
impl<'a> CandidateSourceModuleUse<'a> {
    pub fn position(&self) -> &yu_hir::shadow::PositionId {
        &self.position
    }
    pub fn target_position(&self) -> &yu_hir::shadow::PositionId {
        &self.target_position
    }
    pub fn receiving_position(&self) -> &yu_hir::shadow::PositionId {
        &self.receiving_position
    }
    pub fn observation(&self) -> yu_solver::shadow_apply::CandidateDefinitionUseRef<'a> {
        self.observation
    }
    /// Raw incidence does not supply the missing declaration skeleton.
    pub fn declaration_skeleton(&self) -> Option<&'a Skeleton> {
        None
    }
}

/// Separate module-use observation; the strict formal-call crosswalk above
/// continues to require its exact original SourceCallUseInput.
pub struct CandidateSourceModuleUses<'a> {
    uses: Vec<CandidateSourceModuleUse<'a>>,
}
impl<'a> CandidateSourceModuleUses<'a> {
    pub fn new(
        source: &'a ShadowArtifact,
        hir: &'a HirModule,
        candidate: &'a CandidateValueObservation,
    ) -> Result<Self, CrosswalkError> {
        if !candidate.observes_hir(hir) {
            return Err(CrosswalkError::ForeignCandidate);
        }
        let mut uses = Vec::new();
        let mut validated_source_identity = false;
        for item in hir.items() {
            let HirItem::Binding(binding) = item else {
                if let HirItem::Expression(expression) = item {
                    source
                        .occurrence_source_position(hir, expression.occurrence())
                        .map_err(CrosswalkError::Source)?;
                    validated_source_identity = true;
                }
                continue;
            };
            // Validate source artifact ownership even when this declaration has
            // no module Name occurrences to crosswalk.
            source
                .definition_source_position(hir, binding.definition_root())
                .map_err(CrosswalkError::Source)?;
            validated_source_identity = true;
            let mut pending = vec![binding.value()];
            while let Some(expression) = pending.pop() {
                match expression {
                    ResolvedExpr::Name {
                        occurrence,
                        resolution: yu_hir::NameResolution::Resolved(target),
                        ..
                    } => {
                        let observation = candidate
                            .definition_use(occurrence)
                            .ok_or(CrosswalkError::ForeignCandidate)?;
                        let target_binding = hir
                            .items()
                            .iter()
                            .find_map(|item| match item {
                                HirItem::Binding(b) if b.id() == target => Some(b),
                                _ => None,
                            })
                            .ok_or(CrosswalkError::MissingExactSourceIncidence)?;
                        if observation.target_scheme().owner() != target_binding.definition_root()
                            || observation.receiving_scheme().owner() != binding.definition_root()
                        {
                            return Err(CrosswalkError::ForeignCandidate);
                        }
                        uses.push(CandidateSourceModuleUse {
                            position: source
                                .occurrence_source_position(hir, occurrence)
                                .map_err(CrosswalkError::Source)?,
                            target_position: source
                                .definition_source_position(hir, target_binding.definition_root())
                                .map_err(CrosswalkError::Source)?,
                            receiving_position: source
                                .definition_source_position(hir, binding.definition_root())
                                .map_err(CrosswalkError::Source)?,
                            observation,
                        });
                    }
                    ResolvedExpr::Lambda { body, .. } => pending.push(body),
                    ResolvedExpr::Group { inner, .. } => pending.push(inner),
                    ResolvedExpr::Apply {
                        callee, argument, ..
                    } => {
                        pending.push(callee);
                        pending.push(argument);
                    }
                    _ => {}
                }
            }
        }
        if !validated_source_identity {
            return Err(CrosswalkError::MissingExactSourceIncidence);
        }
        Ok(Self { uses })
    }
    pub fn uses(&self) -> &[CandidateSourceModuleUse<'a>] {
        &self.uses
    }
}
