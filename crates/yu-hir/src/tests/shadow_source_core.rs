//! Detached source/scope/application experiment, not typed elaboration or inference.
//! Only these tests consume `shadow_from_source`; it is never on a production path.
//! Remove this module and its declaration to roll back the experiment. Unsupported
//! source and invalid references return errors without semantic fallback.

use super::*;

#[derive(Debug)]
struct ShadowArtifact {
    identity: Arc<()>,
    binders: Vec<Binder>,
    expressions: Vec<Expression>,
    uses: Vec<ExprId>,
    body: ExprId,
    pending: Vec<PendingPremise>,
}

#[derive(Clone, Debug)]
struct LocalId {
    artifact: Arc<()>,
    index: usize,
}

impl PartialEq for LocalId {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.artifact, &other.artifact) && self.index == other.index
    }
}

impl Eq for LocalId {}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ExprId(LocalId);

#[derive(Clone, Debug, Eq, PartialEq)]
struct BinderId(LocalId);

#[derive(Clone, Debug, Eq, PartialEq)]
struct UseId(LocalId);

#[derive(Debug)]
struct Binder {
    name: String,
    range: Range<usize>,
}

#[derive(Debug)]
struct Expression {
    range: Range<usize>,
    form: Form,
}

#[derive(Debug)]
enum Form {
    Use {
        binder: BinderId,
        occurrence: UseId,
    },
    Group {
        inner: ExprId,
    },
    Apply {
        source_form: SyntaxKind,
        callee: ExprId,
        argument: ExprId,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Premise {
    CallableRole,
    FullFunctionMembership,
    CallViewRealization,
}

#[derive(Debug)]
struct PendingPremise {
    call: ExprId,
    premise: Premise,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ShadowError {
    MalformedSource,
    UnsupportedExpression {
        kind: SyntaxKind,
        range: Range<usize>,
    },
    InvalidRange {
        range: Range<usize>,
    },
    DuplicateBinder {
        range: Range<usize>,
    },
    UnboundName {
        range: Range<usize>,
    },
    ForeignArtifact,
    MissingReference {
        index: usize,
    },
    InvalidUseReference,
    InvalidCallReference,
    InvalidExpressionReference,
}

// This bounded source seam owns only lexical resolution and retained structure.
// The premise registry records missing judgments; it provides no discharge API.
fn shadow_from_source(source: &str) -> Result<ShadowArtifact, ShadowError> {
    let parsed = parsed(source);
    if !parsed
        .syntax_diagnostics()
        .map_err(|_| ShadowError::MalformedSource)?
        .is_empty()
    {
        return Err(ShadowError::MalformedSource);
    }
    let root = SyntaxNode::new_root(parsed.green().clone());
    // The shared envelope is one direct root binding. Root trivia (the four
    // syntax trivia kinds) and the root parser's semicolon separators may
    // surround it; no sibling or enclosing semantic node is discarded.
    let mut statements = Vec::new();
    for element in root.children_with_tokens() {
        if let Some(node) = element.as_node() {
            if node.kind() != SyntaxKind::BindingStatement {
                return Err(ShadowError::MalformedSource);
            }
            statements.push(node.clone());
        } else if !matches!(
            element.kind(),
            SyntaxKind::Whitespace
                | SyntaxKind::Newline
                | SyntaxKind::LineComment
                | SyntaxKind::BlockComment
                | SyntaxKind::Semicolon
        ) {
            return Err(ShadowError::MalformedSource);
        }
    }
    let [statement] = statements.as_slice() else {
        return Err(ShadowError::MalformedSource);
    };
    let header = only_child(statement, SyntaxKind::BindingHeader)?;
    let target = only_child(&header, SyntaxKind::Pattern)?;
    let parts = target.children().collect::<Vec<_>>();
    let Some((name, parameters)) = parts.split_first() else {
        return Err(ShadowError::MalformedSource);
    };
    identifier(name, source)?;
    if parameters.is_empty() {
        return Err(ShadowError::MalformedSource);
    }
    let identity = Arc::new(());
    let mut binders = Vec::<Binder>::new();
    for parameter in parameters {
        if parameter.kind() != SyntaxKind::PatternMlApplicationTail {
            return Err(ShadowError::MalformedSource);
        }
        let pattern = only_child(parameter, SyntaxKind::Pattern)?;
        let binder_node = only_child(&pattern, SyntaxKind::IdentifierPattern)?;
        let (name, range) = identifier(&binder_node, source)?;
        if binders.iter().any(|binder| binder.name == name) {
            return Err(ShadowError::DuplicateBinder { range });
        }
        binders.push(Binder { name, range });
    }
    let body = only_child(statement, SyntaxKind::BindingBody)?;
    let chain = only_child(&body, SyntaxKind::OperatorChain)?;
    let associated = associate_chain_owned(&parsed, chain)
        .map_err(|_| ShadowError::MalformedSource)?
        .into_hir();
    let mut artifact = ShadowArtifact {
        body: ExprId(LocalId {
            artifact: identity.clone(),
            index: 0,
        }),
        identity,
        binders,
        expressions: Vec::new(),
        uses: Vec::new(),
        pending: Vec::new(),
    };
    artifact.body = artifact.lower(&associated, source)?;
    artifact.validate()?;
    Ok(artifact)
}

fn only_child(node: &SyntaxNode, kind: SyntaxKind) -> Result<SyntaxNode, ShadowError> {
    let children = node.children().collect::<Vec<_>>();
    let matching = children
        .iter()
        .filter(|child| child.kind() == kind)
        .collect::<Vec<_>>();
    let [child] = matching.as_slice() else {
        return Err(ShadowError::MalformedSource);
    };
    // Header and statement contain other structural nodes; atomic patterns and
    // the bounded body must not hide additional source operands.
    if matches!(
        node.kind(),
        SyntaxKind::Pattern | SyntaxKind::PatternMlApplicationTail | SyntaxKind::BindingBody
    ) && children.len() != 1
    {
        return Err(ShadowError::MalformedSource);
    }
    Ok((*child).clone())
}

fn identifier(node: &SyntaxNode, source: &str) -> Result<(String, Range<usize>), ShadowError> {
    if node.kind() != SyntaxKind::IdentifierPattern {
        return Err(ShadowError::MalformedSource);
    }
    let tokens = node.children_with_tokens().collect::<Vec<_>>();
    let [token] = tokens.as_slice() else {
        return Err(ShadowError::MalformedSource);
    };
    let Some(token) = token.as_token() else {
        return Err(ShadowError::MalformedSource);
    };
    if token.kind() != SyntaxKind::Identifier {
        return Err(ShadowError::MalformedSource);
    }
    let range = range_of_token(token);
    let text = source
        .get(range.clone())
        .ok_or_else(|| ShadowError::InvalidRange {
            range: range.clone(),
        })?;
    Ok((text.to_owned(), range))
}

impl ShadowArtifact {
    fn id(&self, index: usize) -> LocalId {
        LocalId {
            artifact: self.identity.clone(),
            index,
        }
    }

    fn check_id(&self, id: &LocalId, length: usize) -> Result<(), ShadowError> {
        if !Arc::ptr_eq(&self.identity, &id.artifact) {
            return Err(ShadowError::ForeignArtifact);
        }
        if id.index >= length {
            return Err(ShadowError::MissingReference { index: id.index });
        }
        Ok(())
    }

    fn expression(&self, id: &ExprId) -> Result<&Expression, ShadowError> {
        self.check_id(&id.0, self.expressions.len())?;
        Ok(&self.expressions[id.0.index])
    }

    fn lower(&mut self, expression: &HirExpr, source: &str) -> Result<ExprId, ShadowError> {
        let HirExpr::Value {
            kind,
            range,
            children,
        } = expression
        else {
            return Err(ShadowError::MalformedSource);
        };
        let text = source
            .get(range.clone())
            .ok_or_else(|| ShadowError::InvalidRange {
                range: range.clone(),
            })?;
        let mut is_use = false;
        let form = match (*kind, children.as_slice()) {
            (SyntaxKind::IdentifierExpression, []) => {
                let index = self
                    .binders
                    .iter()
                    .position(|binder| binder.name == text)
                    .ok_or_else(|| ShadowError::UnboundName {
                        range: range.clone(),
                    })?;
                let occurrence = UseId(self.id(self.uses.len()));
                is_use = true;
                Form::Use {
                    binder: BinderId(self.id(index)),
                    occurrence,
                }
            }
            (SyntaxKind::ParenthesizedExpression, [inner]) => Form::Group {
                inner: self.lower(inner, source)?,
            },
            (SyntaxKind::MlArgument | SyntaxKind::CallTail, [callee, argument]) => {
                let callee = self.lower(callee, source)?;
                let argument = self.lower(argument, source)?;
                Form::Apply {
                    source_form: *kind,
                    callee,
                    argument,
                }
            }
            _ => {
                return Err(ShadowError::UnsupportedExpression {
                    kind: *kind,
                    range: range.clone(),
                });
            }
        };
        let id = ExprId(self.id(self.expressions.len()));
        if matches!(form, Form::Apply { .. }) {
            for premise in [
                Premise::CallableRole,
                Premise::FullFunctionMembership,
                Premise::CallViewRealization,
            ] {
                self.pending.push(PendingPremise {
                    call: id.clone(),
                    premise,
                });
            }
        }
        if is_use {
            self.uses.push(id.clone());
        }
        self.expressions.push(Expression {
            range: range.clone(),
            form,
        });
        Ok(id)
    }

    fn validate(&self) -> Result<(), ShadowError> {
        self.expression(&self.body)?;
        for (index, expression) in self.expressions.iter().enumerate() {
            match &expression.form {
                Form::Use { binder, occurrence } => {
                    self.check_id(&binder.0, self.binders.len())?;
                    self.check_id(&occurrence.0, self.uses.len())?;
                    if self.uses[occurrence.0.index] != ExprId(self.id(index)) {
                        return Err(ShadowError::InvalidUseReference);
                    }
                }
                Form::Group { inner } => {
                    self.check_child(inner, index)?;
                }
                Form::Apply {
                    callee, argument, ..
                } => {
                    self.check_child(callee, index)?;
                    self.check_child(argument, index)?;
                }
            }
        }
        for pending in &self.pending {
            if !matches!(self.expression(&pending.call)?.form, Form::Apply { .. }) {
                return Err(ShadowError::InvalidCallReference);
            }
        }
        Ok(())
    }

    fn check_child(&self, child: &ExprId, parent: usize) -> Result<(), ShadowError> {
        self.expression(child)?;
        // Construction publishes children first. This rejects cyclic or forward
        // references before any recursive structural comparison can consume them.
        if child.0.index >= parent {
            return Err(ShadowError::InvalidExpressionReference);
        }
        Ok(())
    }

    fn scoped_candidate(
        &self,
        id: &ExprId,
        occurrence: &mut u32,
    ) -> Result<ResearchScopedExpr, ShadowError> {
        match &self.expression(id)?.form {
            Form::Use { binder, .. } => {
                self.check_id(&binder.0, self.binders.len())?;
                Ok(ResearchScopedExpr::Variable {
                    binder: binder.0.index as u32,
                })
            }
            Form::Group { inner } => self.scoped_candidate(inner, occurrence),
            Form::Apply {
                callee, argument, ..
            } => {
                let current = *occurrence;
                *occurrence += 1;
                Ok(ResearchScopedExpr::Apply {
                    occurrence: current,
                    callee: Box::new(self.scoped_candidate(callee, occurrence)?),
                    argument: Box::new(self.scoped_candidate(argument, occurrence)?),
                })
            }
        }
    }
}

const COMPOSE: &str = "my compose f g x = f (g x)";

#[test]
fn shadow_source_core_retains_compose_structure_and_pending_premises() {
    let artifact = shadow_from_source(COMPOSE).expect("bounded source skeleton");
    let actual_binders = artifact
        .binders
        .iter()
        .map(|binder| (binder.name.as_str(), binder.range.clone()))
        .collect::<Vec<_>>();
    assert_eq!(
        actual_binders,
        vec![("f", 11..12), ("g", 13..14), ("x", 15..16)]
    );
    let outer = artifact.expression(&artifact.body).unwrap();
    assert_eq!(outer.range, 19..26);
    let Form::Apply {
        source_form,
        callee,
        argument,
    } = &outer.form
    else {
        panic!("outer Apply")
    };
    assert_eq!(*source_form, SyntaxKind::MlArgument);
    assert_eq!(artifact.expression(callee).unwrap().range, 19..20);
    let whole_argument = artifact.expression(argument).unwrap();
    assert_eq!(whole_argument.range, 21..26);
    let Form::Group { inner } = &whole_argument.form else {
        panic!("whole grouped argument")
    };
    let inner_call = artifact.expression(inner).unwrap();
    assert_eq!(inner_call.range, 22..25);
    let Form::Apply {
        callee,
        argument,
        source_form,
    } = &inner_call.form
    else {
        panic!("nested Apply")
    };
    assert_eq!(*source_form, SyntaxKind::MlArgument);
    assert_eq!(artifact.expression(callee).unwrap().range, 22..23);
    assert_eq!(artifact.expression(argument).unwrap().range, 24..25);
    for (index, id) in artifact.uses.iter().enumerate() {
        let Form::Use { binder, occurrence } = &artifact.expression(id).unwrap().form else {
            panic!("resolved use")
        };
        assert_eq!(binder.0.index, index);
        assert_eq!(occurrence.0.index, index);
    }
    assert_eq!(artifact.pending.len(), 6);
    for call in [&artifact.body, inner] {
        let premises = artifact
            .pending
            .iter()
            .filter(|pending| &pending.call == call)
            .map(|pending| pending.premise)
            .collect::<Vec<_>>();
        assert_eq!(
            premises,
            vec![
                Premise::CallableRole,
                Premise::FullFunctionMembership,
                Premise::CallViewRealization
            ]
        );
    }
    // Structural validity cannot supply the absent full membership judgment.
    artifact.validate().unwrap();
    assert!(
        artifact
            .pending
            .iter()
            .any(|pending| pending.premise == Premise::FullFunctionMembership)
    );

    let parsed = parsed(COMPOSE);
    let root = SyntaxNode::new_root(parsed.green().clone());
    let statement = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BindingStatement)
        .unwrap();
    let (parameters, candidate) = research_lower_binding_candidate(&statement, &parsed, COMPOSE);
    assert_eq!(
        parameters,
        artifact
            .binders
            .iter()
            .map(|binder| (binder.name.clone(), binder.range.clone()))
            .collect::<Vec<_>>()
    );
    let mut shadow = artifact.scoped_candidate(&artifact.body, &mut 0).unwrap();
    for binder in (0..artifact.binders.len()).rev() {
        shadow = ResearchScopedExpr::Lambda {
            binder: binder as u32,
            body: Box::new(shadow),
        };
    }
    // Both lanes share parsing/association. This compares source/scope/Apply
    // structure only: no current-infer parity, soundness, or principality claim.
    assert_eq!(shadow, candidate);
}

#[test]
fn shadow_source_core_rejects_foreign_and_missing_references() {
    let mut first = shadow_from_source(COMPOSE).unwrap();
    let second = shadow_from_source(COMPOSE).unwrap();
    assert_eq!(
        first.expression(&second.body).unwrap_err(),
        ShadowError::ForeignArtifact
    );
    assert_eq!(
        first
            .expression(&ExprId(first.id(first.expressions.len())))
            .unwrap_err(),
        ShadowError::MissingReference {
            index: first.expressions.len()
        }
    );
    let use_index = first.uses[0].0.index;
    let Form::Use { binder, .. } = &mut first.expressions[use_index].form else {
        panic!("use")
    };
    *binder = BinderId(second.id(0));
    assert_eq!(first.validate(), Err(ShadowError::ForeignArtifact));
    let local_binder = BinderId(first.id(0));
    let Form::Use { binder, occurrence } = &mut first.expressions[use_index].form else {
        panic!("use")
    };
    *binder = local_binder;
    *occurrence = UseId(second.id(0));
    assert_eq!(first.validate(), Err(ShadowError::ForeignArtifact));
    let local_occurrence = UseId(first.id(0));
    let Form::Use { occurrence, .. } = &mut first.expressions[use_index].form else {
        panic!("use")
    };
    *occurrence = local_occurrence;
    first.validate().unwrap();
    let body = first.body.clone();
    let Form::Apply { argument, .. } = &mut first.expressions[body.0.index].form else {
        panic!("Apply")
    };
    *argument = body;
    assert_eq!(
        first.validate(),
        Err(ShadowError::InvalidExpressionReference)
    );
}

#[test]
fn shadow_source_core_rejects_malformed_and_unbound_source() {
    assert!(
        matches!(shadow_from_source("my compose f g x = f (g missing)"), Err(ShadowError::UnboundName { range }) if range == (24..31))
    );
    assert!(shadow_from_source("my compose f g x = f (").is_err());
    assert!(shadow_from_source("my compose f f x = f x").is_err());
}

#[test]
fn shadow_source_core_requires_one_direct_root_binding() {
    for source in [
        format!("{COMPOSE}; missing"),
        format!("{COMPOSE}\nmissing"),
        format!("mod Nested {{{COMPOSE}}}"),
    ] {
        // These are valid parsed files with a binding somewhere inside them,
        // so rejection must come from the detached lane's root envelope check.
        assert!(parsed(&source).syntax_diagnostics().unwrap().is_empty());
        assert!(matches!(
            shadow_from_source(&source),
            Err(ShadowError::MalformedSource)
        ));
    }
    let source = format!(" \n;{COMPOSE};\n ");
    assert!(shadow_from_source(&source).is_ok());
}
