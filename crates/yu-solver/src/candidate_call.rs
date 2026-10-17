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
    pub by_occurrence: HashMap<HirOccurrenceId, usize>,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum FormalRole { Value, Computation }
#[derive(Clone, Debug)]
pub(super) struct FormalRegistrationInput {
    pub owner: SourceRootId,
    pub lambda: usize,
    pub parameter: HirParameterId,
    pub scope: candidate_effect::AnnotationScope,
    pub recipe_position: usize,
    pub native_root: Option<Term>,
    pub role: FormalRole,
    pub entry_effect: Option<u32>,
    pub receiver_body: Option<(HirOccurrenceId, candidate_source::SourceRegionId)>,
}
#[derive(Clone, Debug)]
pub(super) struct FormalNameInput {
    pub owner: SourceRootId,
    pub expression: usize,
    pub registration: usize,
}
#[derive(Clone, Debug)]
pub(super) struct ApplySourceInput {
    pub owner: SourceRootId,
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
    pub introduction: Option<DirectionalIntroduction>,
    pub receiver_attachment: Option<ReceiverBoundaryAttachment>,
}
/// Provisional source attachment only. The nominal scope inventory still owns
/// this scope at its lexical computation region; this is not an expiry rule.
#[derive(Clone, Debug)]
pub(super) struct ReceiverBoundaryAttachment {
    pub registration: usize,
    pub receiver_lambda: HirOccurrenceId,
    pub receiver_body: HirOccurrenceId,
    pub receiver_region: candidate_source::SourceRegionId,
    pub lexical_region: candidate_source::SourceRegionId,
    pub scope: candidate_scope::EffectScopeId,
}
pub struct CandidateReceiverBoundaryAttachment<'a> {
    record: &'a ReceiverBoundaryAttachment,
}
impl CandidateReceiverBoundaryAttachment<'_> {
    pub fn receiver_lambda(&self) -> &HirOccurrenceId { &self.record.receiver_lambda }
    pub fn receiver_body(&self) -> &HirOccurrenceId { &self.record.receiver_body }
    pub fn receiver_region(&self) -> usize { self.record.receiver_region.0 }
    pub fn lexical_region(&self) -> usize { self.record.lexical_region.0 }
    pub fn original_scope(&self) -> u32 { self.record.scope.0 }
}
/// Symbolic candidate evidence only; no handler/filter or row-state consumer.
#[derive(Clone, Debug)]
pub(super) struct DirectionalIntroduction {
    pub registration: usize,
    pub name: usize,
    pub omitted: Arc<candidate_source::OmittedFormal>,
    pub checking: ConstraintOccurrenceId,
    pub cause: CauseId,
    pub demand: Term,
    pub field: FunctionField,
    pub effect: Term,
    pub row: u32,
}
/// A validated occurrence-specific symbolic introduction, never an event grant.
pub struct CandidateDirectionalIntroduction<'a> {
    record: &'a DirectionalIntroduction,
}
impl CandidateDirectionalIntroduction<'_> {
    pub fn original_owner(&self) -> &SourceRootId {
        &self.record.omitted.owner
    }
    pub fn original_lambda(&self) -> &HirOccurrenceId {
        &self.record.omitted.lambda
    }
    pub fn original_formal(&self) -> &HirParameterId {
        &self.record.omitted.formal
    }
    pub fn original_scope(&self) -> &impl std::fmt::Debug {
        &self.record.omitted.scope
    }
    pub fn checking_occurrence(&self) -> &ConstraintOccurrenceId {
        &self.record.checking
    }
    pub fn checking_cause(&self) -> &CauseId {
        &self.record.cause
    }
    pub fn original_demand(&self) -> Term {
        self.record.demand
    }
    pub fn result_effect(&self) -> Term {
        self.record.effect
    }
    pub fn raw_invocation_row(&self) -> u32 {
        self.record.row
    }
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
                checked_capacity_bytes::<(HirOccurrenceId, usize)>(self.by_occurrence.capacity(), "Call occurrence index"),
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
    ModuleNameSourceTypingAndAdmission,
    ModuleUseReceivingExportCorrespondence,
}
/// Borrowed original source construction at an explicitly annotated computation
/// root. Static provenance does not identify a live receiver or authorize a
/// handler, and nested annotation positions are not root members. The native
/// root and entry row borrow retained constructor outputs; this observer does
/// not independently reauthenticate Function, AE, or FreshUse correspondence.
pub struct CandidateComputationSourcePlan<'a> {
    registration: &'a FormalRegistrationInput,
    lambda: &'a LocalSourceExpr,
    parameter: &'a LocalSourceParameter,
    annotation: &'a yu_hir::shadow::SourceAnnotation,
    row: &'a yu_hir::shadow::SourceEffectRow,
}
impl<'a> CandidateComputationSourcePlan<'a> {
    pub fn original_owner(&self) -> &'a SourceRootId { &self.registration.owner }
    pub fn original_lambda(&self) -> &'a HirOccurrenceId { &self.lambda.occurrence }
    pub fn original_formal(&self) -> &'a HirParameterId { &self.parameter.id }
    pub fn annotation(&self) -> &'a yu_hir::shadow::SourceAnnotation { self.annotation }
    pub fn outer_row(&self) -> &'a yu_hir::shadow::SourceEffectRow { self.row }
    pub fn concrete_members(&self) -> &'a [yu_hir::shadow::SourceEffectId] { &self.row.concrete }
    pub fn symbolic_row_variable(&self) -> Option<&'a str> { self.row.variables.first().map(AsRef::as_ref) }
    /// Original retained registration endpoint; no independent Lambda-port or
    /// fresh-use correspondence is asserted by this observation.
    pub fn entry_effect_row(&self) -> u32 { self.registration.entry_effect.expect("validated computation entry") }
    /// The positive Parameter endpoint installed once by source initialization.
    pub fn native_parameter_root(&self) -> Term { self.registration.native_root.expect("validated registration root") }
}

pub(super) fn observe_computation_source_plan<'a>(
    hir: &'a HirModule,
    store: &ConstraintStore,
    state: &'a State,
    index: usize,
) -> Result<Option<CandidateComputationSourcePlan<'a>>, ArtifactMismatch> {
    let registration = state.formals.get(index).ok_or(ArtifactMismatch)?;
    let source = hir.local_source_for(&registration.owner).map_err(|_| ArtifactMismatch)?.ok_or(ArtifactMismatch)?;
    let lambda = source.expressions().get(registration.lambda).ok_or(ArtifactMismatch)?;
    let LocalSourceForm::Lambda { parameter, .. } = &lambda.form else { return Err(ArtifactMismatch); };
    if parameter.id != registration.parameter
        || parameter.id.source_root() != source.source_root()
        || !hir.owns_occurrence(&lambda.occurrence)
        || !scope_owned(source, &lambda.scope)
        || !scope_owned(source, &parameter.scope)
    { return Err(ArtifactMismatch); }
    // initialize_candidate_source_levels checks recipe identity and installs
    // this exact positive Parameter endpoint once; freeze retains that output.
    let root = registration.native_root.ok_or(ArtifactMismatch)?;
    if !matches!(store.term_view(root), Ok(TermView::LiveVariable(row)) if row.kind() == ComponentKind::Value && row.polarity() == Polarity::Positive)
    { return Err(ArtifactMismatch); }
    let annotation = parameter.annotation.as_ref();
    if annotation.is_some_and(|annotation| annotation.owner != registration.owner) { return Err(ArtifactMismatch); }
    let row = annotation.and_then(|annotation| annotation.ty.effects.as_ref());
    if registration.role == FormalRole::Value {
        if row.is_some() || registration.entry_effect.is_some() { return Err(ArtifactMismatch); }
        return Ok(None);
    }
    let annotation = annotation.ok_or(ArtifactMismatch)?;
    let row = row.ok_or(ArtifactMismatch)?;
    if row.variables.len() > 1 || registration.entry_effect.is_none()
    { return Err(ArtifactMismatch); }
    Ok(Some(CandidateComputationSourcePlan { registration, lambda, parameter, annotation, row }))
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
    pub fn owner(&self) -> &'a SourceRootId {
        &self.input.owner
    }
    pub fn source(&self) -> &'a LocalSourceExpr {
        self.expression
    }
    pub fn callee_source(&self) -> &'a LocalSourceExpr {
        self.callee
    }
    /// Candidate-only observation of an already validated direct module-name
    /// callee. It does not inspect solved endpoints or peel source wrappers.
    pub fn module_callee_target(&self) -> Option<&'a yu_hir::DefId> {
        match &self.callee.form {
            LocalSourceForm::Name {
                resolution: LocalSourceResolution::ModuleDef(target),
                ..
            } => Some(target),
            _ => None,
        }
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
    /// The positive Value root retained once from the registration's authentic
    /// parameter recipe at native row initialization. Wrapped and captured uses
    /// borrow this same root; each Call keeps its own callee and demand.
    pub fn native_registered_root(&self) -> Option<Term> {
        self.formal
            .and_then(|(registration, _, _)| registration.native_root)
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
    /// None means no authenticated omitted-formal route in this candidate carrier;
    /// it is not a language-wide claim of absent protection.
    pub fn directional_introduction(&self) -> Option<CandidateDirectionalIntroduction<'a>> {
        self.input
            .introduction
            .as_ref()
            .map(|record| CandidateDirectionalIntroduction { record })
    }
    /// Source-only experimental evidence. It does not change nominal ownership,
    /// FreshUse, handler eligibility or release behavior.
    pub fn experimental_receiver_attachment(&self) -> Option<CandidateReceiverBoundaryAttachment<'_>> {
        self.input.receiver_attachment.as_ref().map(|record| CandidateReceiverBoundaryAttachment { record })
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
        let module_callee = self.call.module_callee_target().is_some();
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
            (
                module_callee,
                PendingCallSupplier::ModuleNameSourceTypingAndAdmission,
            ),
            (
                module_callee,
                PendingCallSupplier::ModuleUseReceivingExportCorrespondence,
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
        Ok(TermView::Leaf(Leaf::IntPositive | Leaf::UnitPositive | Leaf::BoolPositive | Leaf::StrPositive)) => {
            kind == ComponentKind::Value && polarity == Polarity::Positive
        }
        Ok(TermView::Leaf(Leaf::IntNegative | Leaf::UnitNegative | Leaf::BoolNegative | Leaf::StrNegative)) => {
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
        LocalSourceScope::Definition(owner) => source.definition_root() == Some(owner),
        LocalSourceScope::ModuleExpression(root) => source.source_root() == &SourceRootId::Expression(root.clone()),
        LocalSourceScope::Expression(index) => source.expression(index).is_some(),
        LocalSourceScope::CatchArm { catch, arm } => source.expression(catch).is_some_and(|expr| {
            matches!(&expr.form, LocalSourceForm::Catch { arms, .. } if arms.iter().any(|candidate| &candidate.source == arm))
        }),
        LocalSourceScope::Parameter(parameter) => {
            parameter.source_root() == source.source_root()
        }
        LocalSourceScope::LocalInitializer(local) => {
            local.source_root() == source.source_root()
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
    let source = hir
        .local_source_for(&input.owner)
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
                LocalSourceForm::Group { inner } | LocalSourceForm::Ascription { inner, .. } => inner,
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
            || parameter.id.source_root() != source.source_root()
            || !hir.owns_occurrence(&lambda.occurrence)
            || !hir.owns_occurrence(&name.occurrence)
            || !scope_owned(source, &lambda.scope)
            || !scope_owned(source, &parameter.scope)
            || !scope_owned(source, &name.scope)
            || !matches!(&name.form, LocalSourceForm::Name { resolution: LocalSourceResolution::Parameter(id), .. } if id == &parameter.id)
        {
            return Err(ArtifactMismatch);
        }
        let root = registration.native_root.ok_or(ArtifactMismatch)?;
        if !native_port(store, root, ComponentKind::Value, Polarity::Positive) {
            return Err(ArtifactMismatch);
        }
        Some((registration, parameter, name))
    } else {
        None
    };
    if let Some(attachment) = &input.receiver_attachment {
        let Some((registration, _, _)) = formal.as_ref() else { return Err(ArtifactMismatch); };
        let lambda = source.expressions().get(registration.lambda).ok_or(ArtifactMismatch)?;
        let LocalSourceForm::Lambda { body, .. } = &lambda.form else { return Err(ArtifactMismatch); };
        let body = source.expression(body).ok_or(ArtifactMismatch)?;
        let name = state.names.get(input.formal_name.ok_or(ArtifactMismatch)?).ok_or(ArtifactMismatch)?;
        if attachment.registration != name.registration
            || attachment.receiver_lambda != lambda.occurrence
            || attachment.receiver_body != body.occurrence
            || registration.receiver_body.as_ref() != Some(&(body.occurrence.clone(), attachment.receiver_region))
            || input.introduction.is_none()
        { return Err(ArtifactMismatch); }
    }
    match (&input.introduction, formal.as_ref()) {
        (Some(record), Some((registration, parameter, _))) => {
            let lambda = source
                .expressions()
                .get(registration.lambda)
                .ok_or(ArtifactMismatch)?;
            let name_index = input.formal_name.ok_or(ArtifactMismatch)?;
            let name = state.names.get(name_index).ok_or(ArtifactMismatch)?;
            if parameter.annotation.is_some()
                || record.registration != name.registration
                || record.name != name_index
                || record.omitted.owner != registration.owner
                || record.omitted.lambda != lambda.occurrence
                || record.omitted.formal != parameter.id
                || record.omitted.position != parameter.source
                || record.omitted.scope != registration.scope
                || record.checking != input.checking
                || record.cause != input.cause
                || record.demand != native.demand
                || record.field != FunctionField::ResultEffect
                || record.effect != native.invocation_effect
                || record.row != native.invocation_row
            {
                return Err(ArtifactMismatch);
            }
        }
        (None, Some((_, parameter, _))) if parameter.annotation.is_some() => {}
        (None, None) => {}
        _ => return Err(ArtifactMismatch),
    }
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
