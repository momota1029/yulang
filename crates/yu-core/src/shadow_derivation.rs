//! Incomplete structural computation-core projection for the approved candidate.
//! This opt-in consumer borrows HIR identities and leaves all judgments pending.

use yu_hir::shadow::{
    AnnotationOccurrence, BinderId, CaptureUseIncidence, CapturedCallInput, ClosureCorrespondence,
    ExprId, Form, ParameterAnnotationIncidence, PendingPremise, Position, ResolvedCallIncidence,
    ShadowArtifact, Skeleton, SourceCallUseInput, UnresolvedSourceViewPremise, UseId,
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

/// Raw retained structure only; no value/computation or typing judgment is made.
#[derive(Debug)]
pub struct RawStructuralArena<'a> {
    body: &'a ExprId,
    nodes: Vec<RawNode<'a>>,
    annotations: Vec<RawAnnotation<'a>>,
}

impl<'a> RawStructuralArena<'a> {
    /// Publishes atomically after exact identity joins over the same artifact.
    pub fn from_artifact(artifact: &'a ShadowArtifact) -> Option<Self> {
        let skeleton = artifact.skeleton().ok()?;
        skeleton.expression(skeleton.body()).ok()?;
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
            });
        }
        for incidence in skeleton.parameter_annotations() {
            let binder = skeleton.binder(incidence.parameter()).ok()?;
            artifact.position(binder.position()).ok()?;
            let occurrence = artifact.annotation(incidence.annotation()).ok()?;
            let offset = *annotation_offsets.get(&std::ptr::from_ref(occurrence))?;
            if annotations
                .get_mut(offset)?
                .parameter
                .replace(incidence)
                .is_some()
            {
                return None;
            }
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
                    capture: None,
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
            skeleton.binder(input.binder()).ok()?;
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
        Some(Self {
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
}

/// Source occurrence only; absent incidence does not establish annotation absence.
/// The borrowed occurrence retains its pending typed-port/profile correspondence.
#[derive(Debug)]
pub struct RawAnnotation<'a> {
    pub occurrence: &'a AnnotationOccurrence,
    pub position: &'a Position,
    pub parameter: Option<&'a ParameterAnnotationIncidence>,
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
    pub capture: Option<&'a CaptureUseIncidence>,
}
