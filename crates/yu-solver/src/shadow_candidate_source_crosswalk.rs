//! Test-wired, default-off observational crosswalk for independent root Lambdas.
//! Exact source incidence and candidate solver output never discharge premises.
#![cfg(feature = "shadow-apply-candidate")]
#![allow(
    dead_code,
    reason = "test-wired crosswalk APIs are exercised by separate integration targets"
)]

use yu_hir::shadow::{
    CapturedCallInput, Form, PendingPremise, ShadowArtifact, Skeleton, SourceCallUseInput,
    SourceIdentityError,
};
use yu_hir::{DefinitionRootId, HirItem, HirModule, ResolvedExpr};
use yu_solver::shadow_apply::{
    CandidateCall, CandidateExport, CandidateFreshRow, CandidateValueObservation,
};

/// Validates all observed calls using each exact owning declaration before export.
pub struct CandidateSourceCrosswalk<'a> {
    calls: Vec<CandidateSourceCall<'a>>,
    export: CandidateExport<'a>,
    captured: Option<CapturedCallInput<'a>>,
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
        if !candidate.observes_hir(hir) {
            return Err(CrosswalkError::ForeignCandidate);
        }
        if hir
            .shadow_local_binding(root)
            .map_err(CrosswalkError::Source)?
            .is_some()
        {
            return Self::captured(source, hir, candidate, root);
        }
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
        Ok(Self {
            calls,
            export,
            captured: None,
        })
    }
    /// Borrows existing structural topology; every typed premise stays unresolved.
    pub fn captured_input(&self) -> Option<&CapturedCallInput<'a>> {
        self.captured.as_ref()
    }
    fn captured(
        source: &'a ShadowArtifact,
        hir: &'a HirModule,
        candidate: &'a CandidateValueObservation,
        root: &DefinitionRootId,
    ) -> Result<Self, CrosswalkError> {
        let missing = || CrosswalkError::MissingExactSourceIncidence;
        let [HirItem::Binding(binding)] = hir.items() else {
            return Err(missing());
        };
        if binding.definition_root() != root {
            return Err(missing());
        }
        let skeleton = source.skeleton().map_err(|_| missing())?;
        let input = skeleton.captured_call_input().ok_or_else(missing)?;
        let local = hir
            .shadow_local_binding(root)
            .map_err(CrosswalkError::Source)?
            .ok_or_else(missing)?;
        let ResolvedExpr::Lambda {
            parameter: outer, ..
        } = binding.value()
        else {
            return Err(missing());
        };
        let ResolvedExpr::Lambda {
            parameter: inner,
            body,
            ..
        } = &local.initializer
        else {
            return Err(missing());
        };
        let ResolvedExpr::Apply {
            occurrence,
            callee,
            argument,
            ..
        } = body.as_ref()
        else {
            return Err(missing());
        };
        let [call] = candidate.calls() else {
            return Err(missing());
        };
        if &call.occurrence != occurrence
            || &call.callee != callee.occurrence()
            || &call.argument != argument.occurrence()
            || local.local.definition_root() != root
            || local.continuation.local != local.local
            || local.captures.as_ref() != std::slice::from_ref(outer)
            || hir
                .shadow_parameter_local_owner(inner)
                .map_err(CrosswalkError::Source)?
                != Some(&local.local)
            || !matches!(callee.as_ref(), ResolvedExpr::Name { resolution: yu_hir::NameResolution::Parameter(p), .. } if p == outer)
            || !matches!(argument.as_ref(), ResolvedExpr::Name { resolution: yu_hir::NameResolution::Parameter(p), .. } if p == inner)
        {
            return Err(missing());
        }
        let root_expression = skeleton
            .expression(skeleton.body())
            .map_err(|_| missing())?;
        let Form::Lambda { body: bind, .. } = root_expression.form() else {
            return Err(missing());
        };
        let lambda = skeleton
            .expression(input.local_lambda())
            .map_err(|_| missing())?;
        let Form::Lambda {
            parameter: local_parameter,
            ..
        } = lambda.form()
        else {
            return Err(missing());
        };
        let application = skeleton.expression(input.call()).map_err(|_| missing())?;
        let Form::Apply {
            argument: source_argument,
            ..
        } = application.form()
        else {
            return Err(missing());
        };
        let positions = [
            (
                source.definition_source_position(hir, root),
                root_expression.position(),
            ),
            (
                source.parameter_source_position(hir, outer),
                skeleton
                    .binder(input.outer_parameter())
                    .map_err(|_| missing())?
                    .position(),
            ),
            (
                source.local_source_position(hir, &local.local),
                skeleton
                    .binder(input.local_binding())
                    .map_err(|_| missing())?
                    .position(),
            ),
            (
                source.occurrence_source_position(hir, &local.occurrence),
                skeleton.expression(bind).map_err(|_| missing())?.position(),
            ),
            (
                source.occurrence_source_position(hir, local.initializer.occurrence()),
                lambda.position(),
            ),
            (
                source.parameter_source_position(hir, inner),
                skeleton
                    .binder(local_parameter)
                    .map_err(|_| missing())?
                    .position(),
            ),
            (
                source.occurrence_source_position(hir, occurrence),
                application.position(),
            ),
            (
                source.occurrence_source_position(hir, callee.occurrence()),
                input.capture_position(),
            ),
            (
                source.occurrence_source_position(hir, argument.occurrence()),
                skeleton
                    .expression(source_argument)
                    .map_err(|_| missing())?
                    .position(),
            ),
            (
                source.occurrence_source_position(hir, &local.continuation.occurrence),
                skeleton
                    .use_position(input.returned_use())
                    .map_err(|_| missing())?,
            ),
        ];
        for (actual, expected) in positions {
            if actual.map_err(CrosswalkError::Source)? != *expected {
                return Err(missing());
            }
        }
        let source_call = skeleton
            .source_call_use_inputs()
            .find(|call| call.application().expression() == input.call())
            .ok_or_else(missing)?;
        if source_call.binder() != input.outer_parameter()
            || source_call.occurrence() != input.callee_use()
            || candidate.fresh_rows(&call.callee).is_some()
        {
            return Err(missing());
        }
        let export = candidate
            .export(root)
            .map_err(|_| CrosswalkError::ForeignCandidate)?;
        Ok(Self {
            calls: vec![CandidateSourceCall {
                input: source_call,
                candidate: call,
                skeleton,
                observation: candidate,
            }],
            export,
            captured: Some(input),
        })
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
