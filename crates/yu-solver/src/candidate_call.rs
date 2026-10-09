//! Source-owned inputs to pending complete Call construction, never certificates.
use crate::shadow_apply::CandidateEndpoint;
use crate::*;
use yu_hir::shadow::{
    LocalSource, LocalSourceExpr, LocalSourceForm, LocalSourceIndex, LocalSourceParameter,
    LocalSourceResolution, LocalSourceScope,
};

#[derive(Clone, Debug, Default)]
pub(super) struct State {
    pub formals: Vec<FormalRegistrationInput>,
    pub names: Vec<FormalNameInput>,
    pub calls: Vec<ApplySourceInput>,
}
#[derive(Clone, Debug)]
pub(super) struct FormalRegistrationInput {
    pub owner: DefinitionRootId,
    pub lambda: usize,
    pub parameter: HirParameterId,
    pub recipe_position: usize,
}
#[derive(Clone, Debug)]
pub(super) struct FormalNameInput {
    pub owner: DefinitionRootId,
    pub expression: usize,
    pub registration: usize,
}
#[derive(Clone, Debug)]
pub(super) struct ApplySourceInput {
    pub owner: DefinitionRootId,
    pub expression: usize,
    pub callee: LocalSourceIndex,
    pub argument: LocalSourceIndex,
    pub level: u32,
    pub recipe: usize,
    pub callee_value: CandidateEndpoint,
    pub callee_effect: usize,
    pub argument_value: CandidateEndpoint,
    pub argument_effect: usize,
    pub result: usize,
    pub application_effect: usize,
    pub checking: ConstraintOccurrenceId,
    pub cause: CauseId,
    pub formal_name: Option<usize>,
    pub native: Option<NativeInterface>,
}
#[derive(Clone, Copy, Debug)]
pub(super) struct NativeInterface {
    pub callee: Term,
    pub argument: Term,
    pub callee_effect: Term,
    pub argument_effect: Term,
    pub result: Term,
    pub demand: Term,
    pub invocation_effect: Term,
    pub invocation_row: u32,
    pub application_effect: Term,
}
impl State {
    pub fn bytes(&self) -> usize {
        checked_usize_sum(
            [
                checked_capacity_bytes::<FormalRegistrationInput>(
                    self.formals.capacity(),
                    "Call source formal inputs",
                ),
                checked_capacity_bytes::<FormalNameInput>(
                    self.names.capacity(),
                    "Call source lexical inputs",
                ),
                checked_capacity_bytes::<ApplySourceInput>(
                    self.calls.capacity(),
                    "Call source Apply inputs",
                ),
            ],
            "Call source inputs",
        )
    }
}
/// Missing compiler suppliers, not semantic residual constraints.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PendingCallSupplier {
    OriginalRegistrationWholeInterface,
    ActualFormalIntroductionRoute,
    OriginalCheckingExposureAndSeedExposure,
    OriginalGenCall0,
    ArgumentReifyAndWholeCarrier,
    ReceiverDispatchAndCompleteResultFutureInterfaces,
}
/// Every coordinate is still required from the original Gen-Call-0 producer.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OriginalGenCall0Input {
    B,
    X,
    Xi,
    Delta,
    Declaration,
    ArgumentInterface,
    RegisteredRoot,
    CompleteDemand,
    Beta,
    CalleeLexicalUse,
    ArgumentLexicalUse,
    CallOccurrence,
    CheckingOccurrence,
    ImmediateOutputPosition,
    CompleteOutputPosition,
    ElimOrigin,
}
const GEN_CALL_INPUTS: &[OriginalGenCall0Input] = &[
    OriginalGenCall0Input::B,
    OriginalGenCall0Input::X,
    OriginalGenCall0Input::Xi,
    OriginalGenCall0Input::Delta,
    OriginalGenCall0Input::Declaration,
    OriginalGenCall0Input::ArgumentInterface,
    OriginalGenCall0Input::RegisteredRoot,
    OriginalGenCall0Input::CompleteDemand,
    OriginalGenCall0Input::Beta,
    OriginalGenCall0Input::CalleeLexicalUse,
    OriginalGenCall0Input::ArgumentLexicalUse,
    OriginalGenCall0Input::CallOccurrence,
    OriginalGenCall0Input::CheckingOccurrence,
    OriginalGenCall0Input::ImmediateOutputPosition,
    OriginalGenCall0Input::CompleteOutputPosition,
    OriginalGenCall0Input::ElimOrigin,
];
/// Borrows the authentic LocalSource carrier and the generated native interface.
/// Neither scalar checking provenance nor a negative Function is original typing.
pub struct CandidateSourceCall<'a> {
    input: &'a ApplySourceInput,
    expression: &'a LocalSourceExpr,
    callee: &'a LocalSourceExpr,
    argument: &'a LocalSourceExpr,
    native: &'a NativeInterface,
    formal: Option<(
        &'a FormalRegistrationInput,
        &'a LocalSourceParameter,
        &'a LocalSourceExpr,
    )>,
}
impl<'a> CandidateSourceCall<'a> {
    pub fn owner(&self) -> &'a DefinitionRootId {
        &self.input.owner
    }
    pub fn source(&self) -> &'a LocalSourceExpr {
        self.expression
    }
    pub fn callee_source(&self) -> &'a LocalSourceExpr {
        self.callee
    }
    pub fn argument_source(&self) -> &'a LocalSourceExpr {
        self.argument
    }
    pub fn source_level(&self) -> u32 {
        self.input.level
    }
    pub fn checking_occurrence(&self) -> &'a ConstraintOccurrenceId {
        &self.input.checking
    }
    pub fn checking_cause(&self) -> &'a CauseId {
        &self.input.cause
    }
    pub fn native_demand(&self) -> Term {
        self.native.demand
    }
    pub fn native_callee(&self) -> Term {
        self.native.callee
    }
    pub fn native_argument(&self) -> Term {
        self.native.argument
    }
    pub fn native_callee_evaluation_effect(&self) -> Term {
        self.native.callee_effect
    }
    pub fn formal_parameter_recipe_position(&self) -> Option<usize> {
        self.formal
            .map(|(registration, _, _)| registration.recipe_position)
    }
    pub fn native_argument_evaluation_effect(&self) -> Term {
        self.native.argument_effect
    }
    pub fn native_result(&self) -> Term {
        self.native.result
    }
    pub fn native_invocation_effect(&self) -> Term {
        self.native.invocation_effect
    }
    pub fn native_application_effect(&self) -> Term {
        self.native.application_effect
    }
    pub fn formal_registration(&self) -> Option<&'a LocalSourceParameter> {
        self.formal.map(|(_, parameter, _)| parameter)
    }
    pub fn lexical_formal_use(&self) -> Option<&'a LocalSourceExpr> {
        self.formal.map(|(_, _, name)| name)
    }
    pub fn pending_construction(&self) -> PendingCallConstruction<'_, 'a> {
        PendingCallConstruction { call: self }
    }
    pub fn unresolved(&self) -> &'static [crate::shadow_apply::UnresolvedPremise] {
        crate::shadow_apply::UNRESOLVED
    }
}
/// A request tied to one original source Call, retained independently of fresh uses.
pub struct PendingCallConstruction<'b, 'a> {
    call: &'b CandidateSourceCall<'a>,
}
impl<'b, 'a> PendingCallConstruction<'b, 'a> {
    pub fn source_call(&self) -> &'b CandidateSourceCall<'a> {
        self.call
    }
    pub fn original_formation_inputs(&self) -> &'static [OriginalGenCall0Input] {
        GEN_CALL_INPUTS
    }
    pub fn suppliers(&self) -> impl Iterator<Item = PendingCallSupplier> {
        let formal = self.call.formal.is_some();
        [
            (
                formal,
                PendingCallSupplier::OriginalRegistrationWholeInterface,
            ),
            (formal, PendingCallSupplier::ActualFormalIntroductionRoute),
            (
                formal,
                PendingCallSupplier::OriginalCheckingExposureAndSeedExposure,
            ),
            (true, PendingCallSupplier::OriginalGenCall0),
            (true, PendingCallSupplier::ArgumentReifyAndWholeCarrier),
            (
                true,
                PendingCallSupplier::ReceiverDispatchAndCompleteResultFutureInterfaces,
            ),
        ]
        .into_iter()
        .filter_map(|(needed, supplier)| needed.then_some(supplier))
    }
}
fn native_port(
    store: &ConstraintStore,
    term: Term,
    kind: ComponentKind,
    polarity: Polarity,
) -> bool {
    match store.term_view(term) {
        Ok(TermView::LiveVariable(row)) => row.kind() == kind && row.polarity() == polarity,
        Ok(TermView::Leaf(Leaf::IntPositive)) => {
            kind == ComponentKind::Value && polarity == Polarity::Positive
        }
        Ok(TermView::Leaf(Leaf::IntNegative)) => {
            kind == ComponentKind::Value && polarity == Polarity::Negative
        }
        Ok(TermView::PositiveFunction { .. } | TermView::PositiveBottom) => {
            kind == ComponentKind::Value && polarity == Polarity::Positive
        }
        Ok(
            TermView::NegativeFunction { .. } | TermView::NegativeTop | TermView::NegativeBottom,
        ) => kind == ComponentKind::Value && polarity == Polarity::Negative,
        _ => false,
    }
}
fn scope_owned(source: &LocalSource, scope: &LocalSourceScope) -> bool {
    match scope {
        LocalSourceScope::Definition(owner) => owner == source.definition_root(),
        LocalSourceScope::Expression(index) => source.expression(index).is_some(),
        LocalSourceScope::Parameter(parameter) => {
            parameter.definition_root() == source.definition_root()
        }
        LocalSourceScope::LocalInitializer(local) => {
            local.definition_root() == source.definition_root()
        }
    }
}
pub(super) fn observe<'a>(
    hir: &'a HirModule,
    store: &ConstraintStore,
    state: &'a State,
    index: usize,
) -> Result<CandidateSourceCall<'a>, ArtifactMismatch> {
    let input = state.calls.get(index).ok_or(ArtifactMismatch)?;
    if !hir.owns_definition_root(&input.owner) {
        return Err(ArtifactMismatch);
    }
    let source = hir
        .local_source(&input.owner)
        .map_err(|_| ArtifactMismatch)?
        .ok_or(ArtifactMismatch)?;
    let expression = source
        .expressions()
        .get(input.expression)
        .ok_or(ArtifactMismatch)?;
    let LocalSourceForm::Apply {
        callee, argument, ..
    } = &expression.form
    else {
        return Err(ArtifactMismatch);
    };
    if callee != &input.callee
        || argument != &input.argument
        || input.checking.occurrence() != &expression.occurrence
        || input.cause != CauseId::for_occurrence(input.checking.clone())
    {
        return Err(ArtifactMismatch);
    }
    let callee = source.expression(callee).ok_or(ArtifactMismatch)?;
    let argument = source.expression(argument).ok_or(ArtifactMismatch)?;
    if !hir.owns_occurrence(&expression.occurrence)
        || !hir.owns_occurrence(&callee.occurrence)
        || !hir.owns_occurrence(&argument.occurrence)
    {
        return Err(ArtifactMismatch);
    }
    if !scope_owned(source, &expression.scope)
        || !scope_owned(source, &callee.scope)
        || !scope_owned(source, &argument.scope)
    {
        return Err(ArtifactMismatch);
    }
    let native = input.native.as_ref().ok_or(ArtifactMismatch)?;
    match store
        .term_view(native.demand)
        .map_err(|_| ArtifactMismatch)?
    {
        TermView::NegativeFunction {
            argument,
            argument_effect,
            result_effect,
            result,
        } if argument == native.argument
            && argument_effect == native.argument_effect
            && result_effect == native.invocation_effect
            && result == native.result => {}
        _ => return Err(ArtifactMismatch),
    }
    for (term, kind, polarity) in [
        (native.callee, ComponentKind::Value, Polarity::Positive),
        (native.argument, ComponentKind::Value, Polarity::Positive),
        (native.result, ComponentKind::Value, Polarity::Negative),
        (
            native.callee_effect,
            ComponentKind::Effect,
            Polarity::Positive,
        ),
        (
            native.argument_effect,
            ComponentKind::Effect,
            Polarity::Positive,
        ),
        (
            native.invocation_effect,
            ComponentKind::Effect,
            Polarity::Negative,
        ),
        (
            native.application_effect,
            ComponentKind::Effect,
            Polarity::Negative,
        ),
    ] {
        if !native_port(store, term, kind, polarity) {
            return Err(ArtifactMismatch);
        }
    }
    if !matches!(store.term_view(native.invocation_effect), Ok(TermView::LiveVariable(row)) if row.ordinal() == native.invocation_row)
    {
        return Err(ArtifactMismatch);
    }
    let formal = if let Some(name_index) = input.formal_name {
        let name = state.names.get(name_index).ok_or(ArtifactMismatch)?;
        let registration = state
            .formals
            .get(name.registration)
            .ok_or(ArtifactMismatch)?;
        if name.owner != input.owner || registration.owner != input.owner {
            return Err(ArtifactMismatch);
        }
        let lexical_expression = name.expression;
        let name = source
            .expressions()
            .get(lexical_expression)
            .ok_or(ArtifactMismatch)?;
        let mut routed = &input.callee;
        loop {
            let child = source.expression(routed).ok_or(ArtifactMismatch)?;
            if routed.ordinal() as usize == lexical_expression {
                break;
            }
            routed = match &child.form {
                LocalSourceForm::Group { inner } => inner,
                LocalSourceForm::Block {
                    final_expression, ..
                } => final_expression,
                _ => return Err(ArtifactMismatch),
            };
        }
        let lambda = source
            .expressions()
            .get(registration.lambda)
            .ok_or(ArtifactMismatch)?;
        let LocalSourceForm::Lambda { parameter, .. } = &lambda.form else {
            return Err(ArtifactMismatch);
        };
        if parameter.id != registration.parameter
            || parameter.id.definition_root() != source.definition_root()
            || !hir.owns_occurrence(&lambda.occurrence)
            || !hir.owns_occurrence(&name.occurrence)
            || !scope_owned(source, &lambda.scope)
            || !scope_owned(source, &parameter.scope)
            || !scope_owned(source, &name.scope)
            || !matches!(&name.form, LocalSourceForm::Name { resolution: LocalSourceResolution::Parameter(id), .. } if id == &parameter.id)
        {
            return Err(ArtifactMismatch);
        }
        Some((registration, parameter, name))
    } else {
        None
    };
    Ok(CandidateSourceCall {
        input,
        expression,
        callee,
        argument,
        native,
        formal,
    })
}

pub(super) fn same_endpoint(left: CandidateEndpoint, right: CandidateEndpoint) -> bool {
    match (left, right) {
        (CandidateEndpoint::Component(left), CandidateEndpoint::Component(right))
        | (CandidateEndpoint::Parameter(left), CandidateEndpoint::Parameter(right)) => {
            left == right
        }
        _ => false,
    }
}
