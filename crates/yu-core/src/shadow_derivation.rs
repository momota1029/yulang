//! Incomplete structural computation-core projection for the approved candidate.
//! This opt-in consumer borrows HIR identities and leaves all judgments pending.

use yu_hir::shadow::{
    BinderId, CaptureUseIncidence, CapturedCallInput, ClosureCorrespondence, ExprId, Form,
    PendingPremise, ShadowArtifact, Skeleton, UnresolvedSourceViewPremise, UseId,
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
