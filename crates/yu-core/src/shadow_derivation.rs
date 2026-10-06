//! Incomplete structural computation-core projections over retained shadow HIR.
//! This opt-in consumer borrows HIR identities and leaves all judgments pending.

use yu_hir::shadow::{
    AnnotationOccurrence, BinderId, CaptureUseIncidence, CapturedCallInput, ClosureCorrespondence,
    ExprId, Expression, Form, ParameterAnnotationIncidence, PendingPremise, Position,
    ResolvedCallIncidence, RootDeclarationHeader, ShadowArtifact, Skeleton, SourceCallUseInput,
    SourceViewPremiseLocator, UnresolvedSourceViewPremise, UseId,
};

/// Flat, immutable arena. Child offsets are local storage addresses, not lexical IDs.
#[derive(Debug)]
pub struct IncompleteDerivation<'a> {
    nodes: Vec<Node<'a>>,
    root: usize,
}

impl<'a> IncompleteDerivation<'a> {
    /// Rejects unsupported sources or mismatched validated inputs before publication.
    pub fn from_captured_call(
        artifact: &'a ShadowArtifact,
        input: &CapturedCallInput<'_>,
    ) -> Option<Self> {
        if artifact.source() != "my apply f = { my step x = f x; step }" {
            return None;
        }
        let skeleton = artifact.skeleton().ok()?;
        let retained = skeleton.captured_call_input()?;
        if retained.outer_parameter() != input.outer_parameter()
            || retained.local_lambda() != input.local_lambda()
            || retained.local_binding() != input.local_binding()
            || retained.returned_use() != input.returned_use()
            || retained.call() != input.call()
            || retained.callee_use() != input.callee_use()
            || retained.capture_position() != input.capture_position()
        {
            return None;
        }
        let mut arena = Self {
            nodes: Vec::with_capacity(11),
            root: 0,
        };
        arena.root = arena.project(skeleton, skeleton.body(), false)?;
        Some(arena)
    }

    pub fn nodes(&self) -> &[Node<'a>] {
        &self.nodes
    }

    pub fn root(&self) -> usize {
        self.root
    }

    fn push(&mut self, node: Node<'a>) -> usize {
        let offset = self.nodes.len();
        self.nodes.push(node);
        offset
    }

    fn project(&mut self, skeleton: &'a Skeleton, id: &'a ExprId, value: bool) -> Option<usize> {
        let node = match skeleton.expression(id).ok()?.form() {
            Form::Lambda {
                parameter,
                body,
                captures,
                correspondence,
                ..
            } => {
                let body = self.project(skeleton, body, false)?;
                Node::Lambda {
                    source: id,
                    parameter,
                    captures,
                    correspondence,
                    body,
                }
            }
            Form::Bind {
                binder,
                value,
                body,
            } => {
                let value = self.project(skeleton, value, true)?;
                let body = self.project(skeleton, body, false)?;
                Node::Bind {
                    source: id,
                    binder,
                    value,
                    body,
                }
            }
            Form::Use { binder, occurrence } => {
                let name = self.push(Node::Name {
                    source: id,
                    binder,
                    occurrence,
                });
                return Some(self.push(Node::Result { value: name }));
            }
            Form::Apply {
                callee, argument, ..
            } => {
                let callee = self.project(skeleton, callee, false)?;
                let argument = self.project(skeleton, argument, false)?;
                let captured = skeleton.captured_call_input()?;
                Node::PendingCall(PendingCall {
                    source: id,
                    callee,
                    argument,
                    application_premises: skeleton.pending(),
                    capture: skeleton.capture_uses().iter().find(|capture| {
                        capture.lambda() == captured.local_lambda()
                            && capture.occurrence() == captured.callee_use()
                    })?,
                    source_view_premises: captured
                        .source_view_premise_locator()
                        .unresolved_premises(),
                })
            }
            _ => return None,
        };
        let offset = self.push(node);
        Some(if value {
            self.push(Node::Result { value: offset })
        } else {
            offset
        })
    }
}

#[derive(Debug)]
pub enum Node<'a> {
    Lambda {
        source: &'a ExprId,
        parameter: &'a BinderId,
        captures: &'a [BinderId],
        correspondence: &'a ClosureCorrespondence,
        body: usize,
    },
    Bind {
        source: &'a ExprId,
        binder: &'a BinderId,
        value: usize,
        body: usize,
    },
    Result {
        value: usize,
    },
    Name {
        source: &'a ExprId,
        binder: &'a BinderId,
        occurrence: &'a UseId,
    },
    PendingCall(PendingCall<'a>),
}

/// A structural call hole: no endpoint, effect, role, receipt or invocation judgment.
#[derive(Debug)]
pub struct PendingCall<'a> {
    pub source: &'a ExprId,
    pub callee: usize,
    pub argument: usize,
    pub application_premises: &'a [PendingPremise],
    pub capture: &'a CaptureUseIncidence,
    pub source_view_premises: &'static [UnresolvedSourceViewPremise],
}

/// Structural encoding only: neither a typed derivation nor a normalization.
/// The supported envelope requires retained unary declarations. Missing
/// declarations (including multi-parameter headers) are never reconstructed.
/// This opt-in consumer borrows a frozen raw arena and publishes atomically;
/// removing it leaves the exact-candidate and production routes unchanged.
#[derive(Debug)]
pub struct PendingStructuralProjection<'view, 'artifact> {
    raw: &'view RawStructuralArena<'artifact>,
    nodes: Vec<PendingStructuralNode<'view, 'artifact>>,
    body: usize,
    declarations: Vec<usize>,
}

impl<'view, 'artifact> PendingStructuralProjection<'view, 'artifact> {
    /// Opt-in flat projection retaining an exact root syntactic header.
    /// This creates no Lambda, currying, callable stage or typed formal.
    pub fn from_raw_with_header(raw: &'view RawStructuralArena<'artifact>) -> Option<Self> {
        let header = raw.root_header?;
        raw.skeleton.expression(header.body()).ok()?;
        for parameter in header.parameters() {
            raw.skeleton.binder(parameter).ok()?;
        }
        Self::project(raw, true)
    }

    pub fn root_declaration_header(&self) -> Option<&'artifact RootDeclarationHeader> {
        self.raw.root_header
    }

    pub fn from_raw(raw: &'view RawStructuralArena<'artifact>) -> Option<Self> {
        Self::project(raw, false)
    }

    fn project(raw: &'view RawStructuralArena<'artifact>, with_header: bool) -> Option<Self> {
        let offset = |id: &ExprId| {
            let offset = raw.skeleton.expression_offset(id).ok()?;
            (raw.nodes.get(offset)?.source == *id).then_some(offset)
        };
        let body = offset(raw.body)?;
        let mut nodes = Vec::with_capacity(raw.nodes.len());
        let mut declarations = Vec::new();
        // Translate each retained node once. Children are checked addresses;
        // neither traversal nor destruction recurses through expression chains.
        for (index, node) in raw.nodes.iter().enumerate() {
            if offset(&node.source)? != index {
                return None;
            }
            let form = match node.form {
                Form::Lambda {
                    binding,
                    parameter,
                    body,
                    captures,
                    correspondence,
                } => {
                    declarations.push(index);
                    PendingStructuralForm::Lambda {
                        binding,
                        parameter,
                        body: offset(body)?,
                        captures,
                        correspondence,
                    }
                }
                Form::Bind {
                    binder,
                    value,
                    body,
                } => PendingStructuralForm::Bind {
                    binder,
                    value: offset(value)?,
                    body: offset(body)?,
                },
                Form::Use { binder, occurrence } => {
                    PendingStructuralForm::PendingUseNormalization { binder, occurrence }
                }
                Form::IntegerLiteral { spelling } => {
                    PendingStructuralForm::IntegerLiteral { spelling }
                }
                Form::Group { inner } => PendingStructuralForm::Group {
                    inner: offset(inner)?,
                },
                Form::Apply {
                    callee, argument, ..
                } => PendingStructuralForm::PendingApply {
                    callee: offset(callee)?,
                    argument: offset(argument)?,
                    call: node.call.as_ref()?,
                },
            };
            nodes.push(PendingStructuralNode {
                source: &node.source,
                form,
            });
        }
        if declarations.is_empty() && !with_header {
            return None;
        }
        Some(Self {
            raw,
            nodes,
            body,
            declarations,
        })
    }

    pub fn nodes(&self) -> &[PendingStructuralNode<'view, 'artifact>] {
        &self.nodes
    }

    pub fn body(&self) -> usize {
        self.body
    }

    /// Every retained unary declaration, including those outside the body.
    /// This is an inventory, not execution order or a declaration-role judgment.
    pub fn declarations(&self) -> &[usize] {
        &self.declarations
    }

    pub fn annotations(&self) -> &[RawAnnotation<'artifact>] {
        self.raw.annotations()
    }
}

#[derive(Debug)]
pub struct PendingStructuralNode<'view, 'artifact> {
    pub source: &'view ExprId,
    pub form: PendingStructuralForm<'view, 'artifact>,
}

/// No constructor asserts Value/Computation, role, entry, typing or admission.
/// In particular, source Use normalization requires the original Gamma and
/// remains unresolved even when annotation occurrences are retained.
#[derive(Debug)]
pub enum PendingStructuralForm<'view, 'artifact> {
    Lambda {
        binding: &'artifact BinderId,
        parameter: &'artifact BinderId,
        body: usize,
        captures: &'artifact [BinderId],
        correspondence: &'artifact ClosureCorrespondence,
    },
    Bind {
        binder: &'artifact BinderId,
        value: usize,
        body: usize,
    },
    PendingUseNormalization {
        binder: &'artifact BinderId,
        occurrence: &'artifact UseId,
    },
    IntegerLiteral {
        spelling: &'artifact str,
    },
    Group {
        inner: usize,
    },
    /// Only this Apply's raw rows and optional joins are borrowed. The scoped
    /// locator is accessible solely through its validated captured input.
    PendingApply {
        callee: usize,
        argument: usize,
        call: &'view RawCall<'artifact>,
    },
}

/// Raw retained structure only; no value/computation or typing judgment is made.
pub struct RawStructuralArena<'a> {
    root_header: Option<&'a RootDeclarationHeader>,
    skeleton: &'a Skeleton,
    body: &'a ExprId,
    nodes: Vec<RawNode<'a>>,
    annotations: Vec<RawAnnotation<'a>>,
}

impl std::fmt::Debug for RawStructuralArena<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RawStructuralArena")
            .field("body", &self.body)
            .field("nodes", &self.nodes)
            .field("annotations", &self.annotations)
            .finish()
    }
}

impl<'a> RawStructuralArena<'a> {
    /// Publishes atomically after exact identity joins over the same artifact.
    pub fn from_artifact(artifact: &'a ShadowArtifact) -> Option<Self> {
        let skeleton = artifact.skeleton().ok()?;
        skeleton.expression(skeleton.body()).ok()?;
        let root_header = skeleton.root_declaration_header();
        let mut header_parameters = std::collections::HashMap::new();
        if let Some(header) = root_header {
            artifact.position(header.statement()).ok()?;
            artifact.position(header.header()).ok()?;
            artifact.position(header.name()).ok()?;
            skeleton.expression(header.body()).ok()?;
            for parameter in header.parameters() {
                let binder = skeleton.binder(parameter).ok()?;
                if header_parameters
                    .insert(
                        std::ptr::from_ref(binder),
                        RawHeaderParameter { header, parameter },
                    )
                    .is_some()
                {
                    return None;
                }
            }
        }
        let crosswalk = artifact.skeleton_source_crosswalk();
        let mut annotation_offsets = std::collections::HashMap::new();
        let mut annotations = Vec::with_capacity(artifact.annotations().len());
        for occurrence in artifact.annotations() {
            let retained = artifact.annotation(occurrence.id()).ok()?;
            if !std::ptr::eq(retained, occurrence)
                || annotation_offsets
                    .insert(std::ptr::from_ref(retained), annotations.len())
                    .is_some()
            {
                return None;
            }
            annotations.push(RawAnnotation {
                occurrence,
                position: artifact.position(occurrence.position()).ok()?,
                parameter: None,
                header_parameter: None,
            });
        }
        for incidence in skeleton.parameter_annotations() {
            let binder = skeleton.binder(incidence.parameter()).ok()?;
            artifact.position(binder.position()).ok()?;
            let occurrence = artifact.annotation(incidence.annotation()).ok()?;
            let offset = *annotation_offsets.get(&std::ptr::from_ref(occurrence))?;
            let annotation = annotations.get_mut(offset)?;
            if annotation.parameter.replace(incidence).is_some() {
                return None;
            }
            annotation.header_parameter =
                header_parameters.get(&std::ptr::from_ref(binder)).copied();
        }
        let mut nodes = skeleton
            .retained_expressions()
            .map(|(source, expression)| RawNode {
                source,
                form: expression.form(),
                call: matches!(expression.form(), Form::Apply { .. }).then(|| RawCall {
                    application_premises: Vec::new(),
                    direct_use: None,
                    source_use_input: None,
                    parameter_declaration: None,
                    header_parameter: None,
                    capture: None,
                    captured_input: None,
                }),
            })
            .collect::<Vec<_>>();
        // Premises for a call need not be adjacent in the HIR table.
        for premise in skeleton.pending() {
            let offset = skeleton.expression_offset(premise.call()).ok()?;
            nodes
                .get_mut(offset)?
                .call
                .as_mut()?
                .application_premises
                .push(premise);
        }
        for incidence in skeleton.resolved_call_incidences() {
            let offset = skeleton
                .expression_offset(incidence.application().expression())
                .ok()?;
            skeleton.binder(incidence.binder()).ok()?;
            let use_expression = skeleton.use_expression(incidence.occurrence()).ok()?;
            let callee = skeleton.expression(incidence.application().callee()).ok()?;
            if !std::ptr::eq(use_expression, callee) {
                return None;
            }
            if nodes
                .get_mut(offset)?
                .call
                .as_mut()?
                .direct_use
                .replace(incidence)
                .is_some()
            {
                return None;
            }
        }
        // Carry HIR's join, rather than interpreting annotations or reconstructing
        // a callee through wrappers. Validation finishes before arena publication.
        for input in skeleton.source_call_use_inputs() {
            let application = input.application();
            let offset = skeleton.expression_offset(application.expression()).ok()?;
            let expression = skeleton.expression(application.expression()).ok()?;
            let Form::Apply {
                callee, argument, ..
            } = expression.form()
            else {
                return None;
            };
            let Form::Use { binder, occurrence } = skeleton.expression(callee).ok()?.form() else {
                return None;
            };
            if application.callee() != callee
                || input.argument() != argument
                || input.binder() != binder
                || input.occurrence() != occurrence
                || !std::ptr::eq(
                    artifact.position(application.position()).ok()?,
                    artifact.position(expression.position()).ok()?,
                )
            {
                return None;
            }
            skeleton.expression(input.argument()).ok()?;
            let binder = skeleton.binder(input.binder()).ok()?;
            let parameter_declaration =
                match crosswalk.parameter_at_position(binder.position()).ok()? {
                    Some((lambda, parameter)) => {
                        let Form::Lambda {
                            parameter: declared,
                            ..
                        } = lambda.form()
                        else {
                            return None;
                        };
                        if parameter != input.binder() || declared != parameter {
                            return None;
                        }
                        skeleton.binder(parameter).ok()?;
                        Some(RawParameterDeclaration { lambda, parameter })
                    }
                    None => None,
                };
            for incidence in input.parameter_annotations() {
                let occurrence = artifact.annotation(incidence.annotation()).ok()?;
                let annotation =
                    annotations.get(*annotation_offsets.get(&std::ptr::from_ref(occurrence))?)?;
                if incidence.parameter() != input.binder()
                    || !std::ptr::eq(annotation.parameter?, incidence)
                {
                    return None;
                }
            }
            let raw_call = nodes.get_mut(offset)?.call.as_mut()?;
            let direct = raw_call.direct_use.as_ref()?;
            if direct.application().expression() != application.expression()
                || direct.occurrence() != input.occurrence()
                || direct.binder() != input.binder()
                || raw_call.source_use_input.replace(input).is_some()
            {
                return None;
            }
            raw_call.parameter_declaration = parameter_declaration;
            raw_call.header_parameter = header_parameters.get(&std::ptr::from_ref(binder)).copied();
        }
        for capture in skeleton.capture_uses() {
            let call = skeleton.capture_call(capture).ok()?;
            artifact.position(capture.position()).ok()?;
            let offset = skeleton.expression_offset(call).ok()?;
            let raw_call = nodes.get_mut(offset)?.call.as_mut()?;
            let direct = raw_call.direct_use.as_ref()?;
            if direct.occurrence() != capture.occurrence()
                || direct.binder() != capture.captured()
                || raw_call.capture.replace(capture).is_some()
            {
                return None;
            }
        }
        if let Some(input) = skeleton.captured_call_input() {
            let offset = skeleton.expression_offset(input.call()).ok()?;
            let raw_call = nodes.get_mut(offset)?.call.as_mut()?;
            let source = raw_call.source_use_input.as_ref()?;
            let capture = raw_call.capture?;
            if source.application().expression() != input.call()
                || source.occurrence() != input.callee_use()
                || source.binder() != input.outer_parameter()
                || skeleton.capture_call(capture).ok()? != input.call()
                || capture.lambda() != input.local_lambda()
                || capture.captured() != input.outer_parameter()
                || capture.occurrence() != input.callee_use()
                || capture.position() != input.capture_position()
            {
                return None;
            }
            raw_call.captured_input = Some(input);
        }
        Some(Self {
            root_header,
            skeleton,
            body: skeleton.body(),
            nodes,
            annotations,
        })
    }

    pub fn body(&self) -> &ExprId {
        self.body
    }

    pub fn nodes(&self) -> &[RawNode<'a>] {
        &self.nodes
    }

    pub fn annotations(&self) -> &[RawAnnotation<'a>] {
        &self.annotations
    }

    /// Groups only retained direct-use registrations by exact source binder.
    /// Missing registrations establish neither semantic absence nor completeness.
    pub fn pending_binder_use_groups(&self) -> PendingBinderUseGroups<'_, 'a> {
        PendingBinderUseGroups {
            skeleton: self.skeleton,
            nodes: &self.nodes,
        }
    }

    /// Groups every retained resolved source Use by exact binder identity.
    /// This inventory supplies no semantic completeness or absence judgment.
    pub fn source_binder_use_groups(&self) -> SourceBinderUseGroups<'_, 'a> {
        SourceBinderUseGroups {
            skeleton: self.skeleton,
            nodes: &self.nodes,
        }
    }

    /// Borrows candidate bookkeeping positions for one exact retained Apply.
    /// Foreign identities and retained expressions of other forms are rejected.
    /// This performs no typing, inference, semantic association or admission.
    pub fn pending_apply_endpoint_skeleton(
        &self,
        source: &ExprId,
    ) -> Option<PendingApplyEndpointSkeleton<'_, 'a>> {
        let offset = self.skeleton.expression_offset(source).ok()?;
        let node = self.nodes.get(offset)?;
        let expression = self.skeleton.expression(source).ok()?;
        if node.source != *source || !std::ptr::eq(node.form, expression.form()) {
            return None;
        }
        let Form::Apply {
            callee, argument, ..
        } = node.form
        else {
            return None;
        };
        let call = node.call.as_ref()?;
        Some(PendingApplyEndpointSkeleton {
            source: &node.source,
            callee,
            argument,
            call,
            addresses: ApplyStructuralPosition::ALL.map(|position| ApplyStructuralAddress {
                application: &node.source,
                position,
            }),
        })
    }
}

/// Candidate bookkeeping labels only. They assert no typed port, endpoint
/// equality, path, Function applicability, semantics, role, beta/Slots/profile,
/// owner/receiver, original xi, inference result or admission.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ApplyStructuralPosition {
    CalleeValue,
    CalleeEffect,
    ArgumentValue,
    ArgumentEffect,
    CandidateFunctionReturnEffect,
    CandidateFunctionResult,
    WholeApplyValue,
    WholeApplyEffect,
}

impl ApplyStructuralPosition {
    const ALL: [Self; 8] = [
        Self::CalleeValue,
        Self::CalleeEffect,
        Self::ArgumentValue,
        Self::ArgumentEffect,
        Self::CandidateFunctionReturnEffect,
        Self::CandidateFunctionResult,
        Self::WholeApplyValue,
        Self::WholeApplyEffect,
    ];
}

/// Derived address in retained syntax bookkeeping, not a minted endpoint ID.
/// Equality compares only the existing Apply identity and structural label;
/// it asserts no typed endpoint equality or any judgment listed on the label.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ApplyStructuralAddress<'view> {
    application: &'view ExprId,
    position: ApplyStructuralPosition,
}

impl<'view> ApplyStructuralAddress<'view> {
    pub fn application(&self) -> &'view ExprId {
        self.application
    }

    pub fn position(&self) -> ApplyStructuralPosition {
        self.position
    }
}

/// Immutable, incomplete view over a validated retained ordinary Apply.
/// All eight addresses are keyed by this Apply, including its argument labels;
/// these are distinct from a nested argument Apply's whole-result labels.
/// The labels assert no typed port, endpoint equality, path, Function
/// applicability, semantics, role, beta/Slots/profile, owner/receiver, original
/// xi, inference result or admission. All existing premises remain pending,
/// including `OriginalAssocType_X(beta,p0,j_call;s0,c0)`; there is no discharge.
#[derive(Debug)]
pub struct PendingApplyEndpointSkeleton<'view, 'artifact> {
    source: &'view ExprId,
    callee: &'artifact ExprId,
    argument: &'artifact ExprId,
    call: &'view RawCall<'artifact>,
    addresses: [ApplyStructuralAddress<'view>; 8],
}

impl<'view, 'artifact> PendingApplyEndpointSkeleton<'view, 'artifact> {
    pub fn source(&self) -> &'view ExprId {
        self.source
    }

    pub fn callee(&self) -> &'artifact ExprId {
        self.callee
    }

    pub fn argument(&self) -> &'artifact ExprId {
        self.argument
    }

    /// Existing raw metadata and joins, with every premise unchanged.
    pub fn call(&self) -> &'view RawCall<'artifact> {
        self.call
    }

    pub fn addresses(&self) -> &[ApplyStructuralAddress<'view>; 8] {
        &self.addresses
    }
}

/// Source occurrence only; absent incidence does not establish annotation absence.
/// The borrowed occurrence retains its pending typed-port/profile correspondence.
#[derive(Debug)]
pub struct RawAnnotation<'a> {
    pub occurrence: &'a AnnotationOccurrence,
    pub position: &'a Position,
    pub parameter: Option<&'a ParameterAnnotationIncidence>,
    /// Exact root header membership of the existing incidence's binder only.
    pub header_parameter: Option<RawHeaderParameter<'a>>,
}

#[derive(Debug)]
pub struct RawNode<'a> {
    pub source: ExprId,
    pub form: &'a Form,
    pub call: Option<RawCall<'a>>,
}

/// Absent association means unattached metadata, not semantic absence.
#[derive(Debug)]
pub struct RawCall<'a> {
    pub application_premises: Vec<&'a PendingPremise>,
    pub direct_use: Option<ResolvedCallIncidence<'a>>,
    /// Existing HIR reference join only: no formal, slot, typing or admission
    /// judgment. An empty annotation iterator proves neither absence nor completeness.
    pub source_use_input: Option<SourceCallUseInput<'a>>,
    /// Exact source Lambda declaration only; no semantic formal or annotation claim.
    pub parameter_declaration: Option<RawParameterDeclaration<'a>>,
    /// Exact syntactic membership only, distinct from a retained Lambda owner.
    pub header_parameter: Option<RawHeaderParameter<'a>>,
    pub capture: Option<&'a CaptureUseIncidence>,
    captured_input: Option<CapturedCallInput<'a>>,
}

/// Existing root header parameter membership, without callable interpretation.
#[derive(Clone, Copy, Debug)]
pub struct RawHeaderParameter<'a> {
    pub header: &'a RootDeclarationHeader,
    pub parameter: &'a BinderId,
}

/// Borrowed declaration ownership for an exact resolved BinderId. This supplies
/// no callable role, annotation completeness, typed path or premise discharge.
#[derive(Clone, Copy, Debug)]
pub struct RawParameterDeclaration<'a> {
    pub lambda: &'a Expression,
    pub parameter: &'a BinderId,
}

impl<'artifact> RawNode<'artifact> {
    /// Borrowed structural registration for an exact immediate resolved Use.
    /// This supplies no call-view judgment or premise discharge.
    pub fn pending_source_call_registration(
        &self,
    ) -> Option<PendingSourceCallRegistration<'_, 'artifact>> {
        let call = self.call.as_ref()?;
        let source_use_input = call.source_use_input.as_ref()?;
        Some(PendingSourceCallRegistration {
            source: &self.source,
            application: self.form,
            source_use_input,
            parameter_declaration: call.parameter_declaration.as_ref(),
            header_parameter: call.header_parameter.as_ref(),
            application_premises: &call.application_premises,
            capture: call.capture,
            captured_input: call.captured_input.as_ref(),
        })
    }
}

/// Immutable references already joined by the raw arena. Missing topology
/// association establishes no validated match, not semantic absence. Scoped
/// source-view requirements are distinct from ordinary application pending rows.
#[derive(Debug)]
pub struct PendingSourceCallRegistration<'registration, 'artifact> {
    pub source: &'registration ExprId,
    pub application: &'artifact Form,
    pub source_use_input: &'registration SourceCallUseInput<'artifact>,
    pub parameter_declaration: Option<&'registration RawParameterDeclaration<'artifact>>,
    pub header_parameter: Option<&'registration RawHeaderParameter<'artifact>>,
    pub application_premises: &'registration [&'artifact PendingPremise],
    pub capture: Option<&'artifact CaptureUseIncidence>,
    pub captured_input: Option<&'registration CapturedCallInput<'artifact>>,
}

/// Lazy borrowed grouping of existing registrations, with no semantic interface,
/// slot inventory or applicability judgment. Querying a binder scans the retained
/// nodes once; yielded registrations preserve the arena's retained-node order.
#[derive(Debug)]
pub struct PendingBinderUseGroups<'registration, 'artifact> {
    skeleton: &'artifact Skeleton,
    nodes: &'registration [RawNode<'artifact>],
}

/// Existing source identities only, borrowed without interpreting the use's role.
#[derive(Debug)]
pub struct SourceUse<'view, 'artifact> {
    pub source: &'view ExprId,
    pub binder: &'artifact BinderId,
    pub occurrence: &'artifact UseId,
}

/// Lazy inventory of all retained Form::Use occurrences, including uses without
/// direct-call registrations. Each exhausted query scans O(E) retained nodes
/// with O(1) extra memory and preserves arena order. This supplies no typing,
/// applicability, completeness, semantic absence, beta, slot, profile or role
/// judgment and does not discharge any pending premise.
#[derive(Debug)]
pub struct SourceBinderUseGroups<'view, 'artifact> {
    skeleton: &'artifact Skeleton,
    nodes: &'view [RawNode<'artifact>],
}

impl<'artifact> SourceBinderUseGroups<'_, 'artifact> {
    /// Rejects foreign or invalid binders before scanning retained occurrences.
    pub fn uses_for_binder<'query>(
        &'query self,
        binder: &'query BinderId,
    ) -> Option<impl Iterator<Item = SourceUse<'query, 'artifact>> + 'query> {
        self.skeleton.binder(binder).ok()?;
        Some(self.nodes.iter().filter_map(move |node| {
            let Form::Use {
                binder: retained,
                occurrence,
            } = node.form
            else {
                return None;
            };
            (retained == binder).then_some(SourceUse {
                source: &node.source,
                binder: retained,
                occurrence,
            })
        }))
    }
}

impl<'artifact> PendingBinderUseGroups<'_, 'artifact> {
    /// Foreign or invalid identities are rejected. An empty valid group means
    /// only that no existing direct-use registration is attached to this binder.
    pub fn registrations_for_binder<'query>(
        &'query self,
        binder: &'query BinderId,
    ) -> Option<impl Iterator<Item = PendingSourceCallRegistration<'query, 'artifact>> + 'query>
    {
        self.skeleton.binder(binder).ok()?;
        Some(self.nodes.iter().filter_map(move |node| {
            let registration = node.pending_source_call_registration()?;
            (registration.source_use_input.binder() == binder).then_some(registration)
        }))
    }
}

impl PendingSourceCallRegistration<'_, '_> {
    pub fn source_view_premise_locator(&self) -> Option<SourceViewPremiseLocator<'_, '_>> {
        Some(self.captured_input?.source_view_premise_locator())
    }
}
