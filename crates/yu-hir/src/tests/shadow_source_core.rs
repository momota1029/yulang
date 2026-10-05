//! Structural differential consumer of the sole shadow builder.
use super::*;
use crate::shadow::*;
fn shadow_from_source(source: &str) -> Result<Skeleton, ShadowError> {
    let artifact = ShadowArtifact::from_parsed(parsed(source))?;
    artifact.into_skeleton()
}
fn scoped_candidate(
    artifact: &Skeleton,
    id: &ExprId,
    occurrence: &mut u32,
) -> Result<ResearchScopedExpr, ShadowError> {
    match &artifact.expression(id)?.form {
        Form::Lambda { .. } | Form::Bind { .. } => Err(ShadowError::UnsupportedExpression {
            kind: if matches!(artifact.expression(id)?.form, Form::Lambda { .. }) {
                SyntaxKind::BindingStatement
            } else {
                SyntaxKind::BracedStatementBlockExpression
            },
            range: artifact.expression(id)?.range.clone(),
        }),
        Form::IntegerLiteral { .. } => Err(ShadowError::UnsupportedExpression {
            kind: SyntaxKind::IntegerLiteral,
            range: artifact.expression(id)?.range.clone(),
        }),
        Form::Use { binder, .. } => Ok(ResearchScopedExpr::Variable {
            binder: artifact.binder_index(binder)? as u32,
        }),
        Form::Group { inner } => scoped_candidate(artifact, inner, occurrence),
        Form::Apply {
            callee, argument, ..
        } => {
            let current = *occurrence;
            *occurrence += 1;
            Ok(ResearchScopedExpr::Apply {
                occurrence: current,
                callee: Box::new(scoped_candidate(artifact, callee, occurrence)?),
                argument: Box::new(scoped_candidate(artifact, argument, occurrence)?),
            })
        }
    }
}
const COMPOSE: &str = "my compose f g x = f (g x)";

#[test]
fn shadow_source_core_retains_integer_spelling_and_range_without_judgment() {
    let artifact = shadow_from_source("my f x = 42").expect("bounded integer source skeleton");
    assert_eq!(artifact.binders.len(), 1);
    assert_eq!(artifact.binders[0].name, "x");
    assert_eq!(artifact.binders[0].range, 5..6);
    let body = artifact.expression(&artifact.body).unwrap();
    assert_eq!(body.range, 9..11);
    let Form::IntegerLiteral { spelling } = &body.form else {
        panic!("integer literal")
    };
    assert_eq!(spelling, "42");
    assert_eq!(artifact.expressions.len(), 1);
    assert!(artifact.uses.is_empty());
    assert!(artifact.pending.is_empty());
}

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
        assert_eq!(artifact.binder_index(binder).unwrap(), index);
        assert_eq!(artifact.use_index(occurrence).unwrap(), index);
    }
    // FVIEW §§2,5 require unresolved shared-component source formation; counting
    // its per-call reference records that obligation without semantic acceptance.
    assert_eq!(artifact.pending.len(), 8);
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
                Premise::CallViewRealization,
                Premise::QIndependentSourceCallViewFormation
            ]
        );
    }
    // Structural validity cannot supply the absent full membership judgment.

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
    let mut shadow = scoped_candidate(&artifact, &artifact.body, &mut 0).unwrap();
    for binder in (0..artifact.binders.len()).rev() {
        shadow = ResearchScopedExpr::Lambda {
            binder: binder as u32,
            body: Box::new(shadow),
        };
    }
    // Both lanes share parsing but use distinct association/projection paths.
    // This compares source/scope/Apply structure only: no current-infer parity,
    // soundness, or principality claim.
    assert_eq!(shadow, candidate);
}

#[test]
fn shadow_source_core_rejects_foreign_and_missing_references() {
    let first = shadow_from_source(COMPOSE).unwrap();
    let second = shadow_from_source(COMPOSE).unwrap();
    assert_eq!(
        first.expression(&second.body).unwrap_err(),
        ShadowError::ForeignArtifact
    );
    assert_eq!(
        first.binder(&second.binder_ids()[0]).unwrap_err(),
        ShadowError::ForeignArtifact
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

#[test]
fn shadow_source_core_links_distinct_uses_to_exact_retained_positions() {
    let source = "my repeated x = x x";
    let first = ShadowArtifact::from_parsed(parsed(source)).unwrap();
    let second = ShadowArtifact::from_parsed(parsed(source)).unwrap();
    let skeleton = first.skeleton().unwrap();
    let uses = skeleton
        .uses()
        .iter()
        .map(|id| {
            let Form::Use { binder, occurrence } = skeleton.expression(id).unwrap().form() else {
                panic!("resolved use")
            };
            (
                binder,
                occurrence,
                skeleton.use_position(occurrence).unwrap(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(uses.len(), 2);
    assert_eq!(uses[0].0, uses[1].0);
    assert_ne!(uses[0].1, uses[1].1);
    assert_ne!(uses[0].2, uses[1].2);
    let binder = skeleton.binder(uses[0].0).unwrap();
    let position = first.position(binder.position()).unwrap();
    assert_eq!(position.kind(), SyntaxKind::IdentifierPattern);
    assert!(position.is_node());
    assert_eq!(position.range(), &(12..13));
    // Reconstruct CST occurrence paths using parent/ordinal identity, independently
    // of spelling and ranges (both uses have the same spelling).
    let root = SyntaxNode::new_root(first.parsed().green().clone());
    for (index, (_, _, id)) in uses.iter().enumerate() {
        let position = first.position(id).unwrap();
        assert_eq!(position.kind(), SyntaxKind::IdentifierExpression);
        assert_eq!(position.range(), &(16 + index * 2..17 + index * 2));
        let mut path = Vec::new();
        let mut current = *id;
        while let Some(parent) = first.position(current).unwrap().parent() {
            path.push(first.position(current).unwrap().ordinal());
            current = parent;
        }
        let mut node = root.clone();
        for ordinal in path.into_iter().rev() {
            node = node
                .children_with_tokens()
                .nth(ordinal)
                .unwrap()
                .into_node()
                .unwrap();
        }
        assert_eq!(node.kind(), position.kind());
        assert_eq!(range_of(&node), *position.range());
        assert_eq!(node.to_string(), "x");
        assert_eq!(
            second.position(id).unwrap_err(),
            ShadowError::ForeignArtifact
        );
        assert_eq!(
            second
                .skeleton()
                .unwrap()
                .use_position(uses[index].1)
                .unwrap_err(),
            ShadowError::ForeignArtifact
        );
    }
    assert_eq!(
        second.position(binder.position()).unwrap_err(),
        ShadowError::ForeignArtifact
    );
    assert_eq!(
        second.skeleton().unwrap().binder(uses[0].0).unwrap_err(),
        ShadowError::ForeignArtifact
    );
}

// Private exact-candidate projection: locators identify raw CST occurrences,
// while spelling is used only by the ordinary lexical environment.
#[derive(Clone, Debug, Eq, PartialEq)]
struct NestedLocator {
    path: Vec<usize>,
    kind: SyntaxKind,
    range: Range<usize>,
}

fn nested_source_locator(node: &SyntaxNode) -> NestedLocator {
    let mut path = Vec::new();
    let mut current = node.clone();
    while let Some(parent) = current.parent() {
        path.push(
            parent
                .children_with_tokens()
                .position(|child| child.as_node() == Some(&current))
                .unwrap(),
        );
        current = parent;
    }
    path.reverse();
    NestedLocator {
        path,
        kind: node.kind(),
        range: range_of(node),
    }
}

fn nested_shadow_locator(artifact: &ShadowArtifact, id: &PositionId) -> NestedLocator {
    let position = artifact.position(id).unwrap();
    let mut current = id.clone();
    let mut path = Vec::new();
    while let Some(parent) = artifact.position(&current).unwrap().parent() {
        path.push(artifact.position(&current).unwrap().ordinal());
        current = parent.clone();
    }
    path.reverse();
    NestedLocator {
        path,
        kind: position.kind(),
        range: position.range().clone(),
    }
}

#[derive(Debug, Eq, PartialEq)]
enum NestedSourceExpr {
    Lambda {
        position: NestedLocator,
        binding: NestedLocator,
        parameter: NestedLocator,
        captures: Vec<NestedLocator>,
        body: Box<Self>,
    },
    Bind {
        position: NestedLocator,
        binder: NestedLocator,
        value: Box<Self>,
        body: Box<Self>,
    },
    Apply {
        position: NestedLocator,
        range: Range<usize>,
        callee: Box<Self>,
        argument: Box<Self>,
    },
    Use {
        position: NestedLocator,
        binder: NestedLocator,
    },
}

fn nested_normalize_shadow(artifact: &ShadowArtifact, id: &ExprId) -> NestedSourceExpr {
    let skeleton = artifact.skeleton().unwrap();
    let expression = skeleton.expression(id).unwrap();
    let position = nested_shadow_locator(artifact, expression.position());
    let binder = |id| nested_shadow_locator(artifact, skeleton.binder(id).unwrap().position());
    match expression.form() {
        Form::Lambda {
            binding,
            parameter,
            captures,
            body,
            correspondence,
        } => {
            assert_eq!(
                *correspondence,
                ClosureCorrespondence::PendingTypedCaptureProviderReceiverAndSemanticDischarge
            );
            NestedSourceExpr::Lambda {
                position,
                binding: binder(binding),
                parameter: binder(parameter),
                captures: captures.iter().map(binder).collect(),
                body: Box::new(nested_normalize_shadow(artifact, body)),
            }
        }
        Form::Bind {
            binder: bound,
            value,
            body,
        } => NestedSourceExpr::Bind {
            position,
            binder: binder(bound),
            value: Box::new(nested_normalize_shadow(artifact, value)),
            body: Box::new(nested_normalize_shadow(artifact, body)),
        },
        Form::Apply {
            source_form,
            callee,
            argument,
        } => {
            assert_eq!(*source_form, SyntaxKind::MlArgument);
            NestedSourceExpr::Apply {
                position,
                range: expression.range().clone(),
                callee: Box::new(nested_normalize_shadow(artifact, callee)),
                argument: Box::new(nested_normalize_shadow(artifact, argument)),
            }
        }
        Form::Use {
            binder: bound,
            occurrence,
        } => {
            assert_eq!(
                nested_shadow_locator(artifact, skeleton.use_position(occurrence).unwrap()),
                position
            );
            NestedSourceExpr::Use {
                position,
                binder: binder(bound),
            }
        }
        _ => panic!("only the approved nested candidate structure"),
    }
}

#[test]
fn shadow_source_core_nested_candidate_matches_independent_cst_projection() {
    const SOURCE: &str = "my apply f = { my step x = f x; step }";
    let parsed = parsed(SOURCE);
    let root = SyntaxNode::new_root(parsed.green().clone());
    let child = |node: &SyntaxNode, kind| {
        let matches = node
            .children()
            .filter(|node| node.kind() == kind)
            .collect::<Vec<_>>();
        assert_eq!(matches.len(), 1);
        matches[0].clone()
    };
    let header = |binding: &SyntaxNode| {
        let pattern = child(
            &child(binding, SyntaxKind::BindingHeader),
            SyntaxKind::Pattern,
        );
        let name = child(&pattern, SyntaxKind::IdentifierPattern);
        let tail = child(&pattern, SyntaxKind::PatternMlApplicationTail);
        let parameter = child(
            &child(&tail, SyntaxKind::Pattern),
            SyntaxKind::IdentifierPattern,
        );
        (name, parameter)
    };
    let outer = child(&root, SyntaxKind::BindingStatement);
    let (apply, f) = header(&outer);
    let block = child(
        &child(
            &child(&outer, SyntaxKind::BindingBody),
            SyntaxKind::OperatorChain,
        ),
        SyntaxKind::BracedStatementBlockExpression,
    );
    let statements = block
        .children()
        .filter(|node| node.kind() == SyntaxKind::Statement)
        .collect::<Vec<_>>();
    assert_eq!(statements.len(), 2);
    let separator = child(&block, SyntaxKind::BlockStatementSeparator);
    assert_eq!(separator.to_string().trim(), ";");
    let local = child(&statements[0], SyntaxKind::BindingStatement);
    let (step, x) = header(&local);
    let call_chain = child(
        &child(&local, SyntaxKind::BindingBody),
        SyntaxKind::OperatorChain,
    );
    let callee = child(&call_chain, SyntaxKind::IdentifierExpression);
    let call_tail = child(&call_chain, SyntaxKind::MlArgument);
    let argument = child(
        &child(&call_tail, SyntaxKind::OperatorChain),
        SyntaxKind::IdentifierExpression,
    );
    let returned = child(
        &child(&statements[1], SyntaxKind::OperatorChain),
        SyntaxKind::IdentifierExpression,
    );
    for (node, kind, range) in [
        (&outer, SyntaxKind::BindingStatement, 0..38),
        (&apply, SyntaxKind::IdentifierPattern, 3..8),
        (&f, SyntaxKind::IdentifierPattern, 9..10),
        (&block, SyntaxKind::BracedStatementBlockExpression, 13..38),
        (&local, SyntaxKind::BindingStatement, 15..30),
        (&step, SyntaxKind::IdentifierPattern, 18..22),
        (&x, SyntaxKind::IdentifierPattern, 23..24),
        (&callee, SyntaxKind::IdentifierExpression, 27..28),
        (&call_tail, SyntaxKind::MlArgument, 29..30),
        (&argument, SyntaxKind::IdentifierExpression, 29..30),
        (&returned, SyntaxKind::IdentifierExpression, 32..36),
    ] {
        assert_eq!(node.kind(), kind);
        assert_eq!(range_of(node), range);
    }
    let associated = associate_chain_owned(&parsed, call_chain)
        .unwrap()
        .into_hir();
    let ResearchApply::Apply {
        form,
        range,
        callee: associated_callee,
        argument: associated_argument,
        ..
    } = research_lower_apply(&associated, SOURCE, &mut 0)
    else {
        panic!("one ordinary call")
    };
    assert_eq!(form, SyntaxKind::MlArgument);
    assert_eq!(range, 27..30);
    for (expression, node) in [
        (&*associated_callee, &callee),
        (&*associated_argument, &argument),
    ] {
        let ResearchApply::Atom { name, range } = expression else {
            panic!("identifier operand")
        };
        assert_eq!(*range, range_of(node));
        assert_eq!(name, &node.to_string());
    }
    let mut environment = vec![(f.to_string(), nested_source_locator(&f))];
    let resolve = |node: &SyntaxNode, environment: &[(String, NestedLocator)]| {
        let binder = environment
            .iter()
            .rev()
            .find(|(name, _)| name == &node.to_string())
            .unwrap()
            .1
            .clone();
        NestedSourceExpr::Use {
            position: nested_source_locator(node),
            binder,
        }
    };
    environment.push((x.to_string(), nested_source_locator(&x)));
    let resolved_callee = resolve(&callee, &environment);
    let NestedSourceExpr::Use {
        binder: captured, ..
    } = &resolved_callee
    else {
        panic!("captured callee use")
    };
    let captured = captured.clone();
    assert_ne!(captured, nested_source_locator(&x));
    let call = NestedSourceExpr::Apply {
        position: nested_source_locator(&call_tail),
        range,
        callee: Box::new(resolved_callee),
        argument: Box::new(resolve(&argument, &environment)),
    };
    environment.pop();
    let local_lambda = NestedSourceExpr::Lambda {
        position: nested_source_locator(&local),
        binding: nested_source_locator(&step),
        parameter: nested_source_locator(&x),
        captures: vec![captured],
        body: Box::new(call),
    };
    // Publish step only after its initializer; x ends with the local lambda.
    environment.push((step.to_string(), nested_source_locator(&step)));
    let candidate = NestedSourceExpr::Lambda {
        position: nested_source_locator(&outer),
        binding: nested_source_locator(&apply),
        parameter: nested_source_locator(&f),
        captures: vec![],
        body: Box::new(NestedSourceExpr::Bind {
            position: nested_source_locator(&block),
            binder: nested_source_locator(&step),
            value: Box::new(local_lambda),
            body: Box::new(resolve(&returned, &environment)),
        }),
    };
    let artifact = ShadowArtifact::from_parsed(parsed).unwrap();
    let skeleton = artifact.skeleton().unwrap();
    assert_eq!(
        nested_normalize_shadow(&artifact, skeleton.body()),
        candidate
    );
    assert_eq!(skeleton.expressions().len(), 7);
    assert_eq!(skeleton.binders().len(), 4);
    assert_eq!(skeleton.uses().len(), 3);
    let [incidence] = skeleton.capture_uses() else {
        panic!("one capture-use incidence")
    };
    assert_eq!(
        nested_shadow_locator(
            &artifact,
            skeleton.expression(incidence.lambda()).unwrap().position()
        ),
        nested_source_locator(&local)
    );
    assert_eq!(
        nested_shadow_locator(
            &artifact,
            skeleton.binder(incidence.captured()).unwrap().position()
        ),
        nested_source_locator(&f)
    );
    assert_eq!(
        nested_shadow_locator(
            &artifact,
            skeleton
                .use_expression(incidence.occurrence())
                .unwrap()
                .position()
        ),
        nested_source_locator(&callee)
    );
    assert_eq!(
        nested_shadow_locator(&artifact, incidence.position()),
        nested_source_locator(&callee)
    );
    assert_eq!(skeleton.pending().len(), 4);
    for (pending, premise) in skeleton.pending().iter().zip([
        Premise::CallableRole,
        Premise::FullFunctionMembership,
        Premise::CallViewRealization,
        Premise::QIndependentSourceCallViewFormation,
    ]) {
        assert_eq!(pending.premise(), premise);
        assert_eq!(
            nested_shadow_locator(
                &artifact,
                skeleton.expression(pending.call()).unwrap().position()
            ),
            nested_source_locator(&call_tail)
        );
    }
    // This differential supplies lexical source structure only. Typed capture,
    // provider/receiver, receipt, O/A, Q registration and nu/K/D remain open;
    // it claims neither a semantic theorem nor production-infer parity.
}
