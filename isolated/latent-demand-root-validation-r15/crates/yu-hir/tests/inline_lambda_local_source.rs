#![cfg(feature = "shadow")]

use std::collections::HashSet;
use std::sync::Arc;
use yu_hir::shadow::{
    LocalSource, LocalSourceForm, LocalSourceResolution, LocalSourceScope, ParameterSourceOrigin,
    ShadowArtifact, SourceIdentityError, lower_module_with_local_source,
};
use yu_hir::{
    FileId, FileKey, HirAvailabilityError, HirItem, HirModule, ModuleIdentity, SemanticImports,
};
use yu_syntax::{ParsedFile, SourceText, SyntaxEnvironment, SyntaxKind, parse_file, scan_header};

fn parsed(text: &str) -> ParsedFile {
    let source: Arc<SourceText> = Arc::from(text);
    parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    )
}
fn lower_parse(parsed: &ParsedFile) -> Result<HirModule, HirAvailabilityError> {
    lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("test", "inline.yu"))),
        parsed,
        SemanticImports::empty(),
    )
}
fn lower(text: &str) -> HirModule {
    lower_parse(&parsed(text)).unwrap()
}
fn source(module: &HirModule) -> &LocalSource {
    let HirItem::Binding(binding) = &module.items()[0] else {
        panic!("binding");
    };
    module
        .local_source(binding.definition_root())
        .unwrap()
        .unwrap()
}

#[test]
fn identity_constant_and_generic_identifier_binders() {
    for name in ["x", "_", "変数", "ready?"] {
        let module = lower(&format!("my value = \\{name} -> {name}"));
        let source = source(&module);
        let expression = source.expression(source.body()).unwrap();
        let LocalSourceForm::Lambda { parameter, body } = &expression.form else {
            panic!("lambda");
        };
        assert_eq!(parameter.spelling.as_ref(), name);
        assert!(parameter.annotation.is_none());
        assert!(matches!(expression.scope, LocalSourceScope::Definition(_)));
        assert!(
            matches!(&source.expression(body).unwrap().scope, LocalSourceScope::Parameter(id) if id == &parameter.id)
        );
        assert!(matches!(&source.expression(body).unwrap().form,
            LocalSourceForm::Name { resolution: LocalSourceResolution::Parameter(id), .. } if id == &parameter.id));
        assert!(source.named_groups().is_empty());
        assert!(source.bindings().is_empty());
    }
    for name in ["x", "if", "catch"] {
        let text = format!("my value = \\{name} -> 1");
        let parse = parsed(&text);
        let module = lower_parse(&parse).unwrap();
        let source = source(&module);
        let LocalSourceForm::Lambda { body, .. } = &source.expression(source.body()).unwrap().form
        else {
            panic!("lambda");
        };
        let body = source.expression(body).unwrap();
        let LocalSourceForm::Integer(raw) = &body.form else {
            panic!("integer body: {:?}", body.form);
        };
        let artifact = ShadowArtifact::from_parsed(parse.clone()).unwrap();
        let position = artifact.source_position(&body.source).unwrap();
        let node = artifact.position(&position).unwrap();
        assert_eq!(node.kind(), SyntaxKind::IntegerLiteral);
        assert_eq!(node.range(), &body.range);
        let root = yu_syntax::SyntaxNode::new_root(parse.green().clone());
        let tokens: Vec<_> = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| {
                token.kind() == SyntaxKind::Integer
                    && usize::from(token.text_range().start()) >= body.range.start
                    && usize::from(token.text_range().end()) <= body.range.end
            })
            .collect();
        assert_eq!(tokens.len(), 1);
        assert_eq!(raw.as_ref(), tokens[0].text());
        assert_eq!(tokens[0].text(), "1");
    }
}

#[test]
fn nested_nearest_shadowing_and_original_root_capture() {
    for (text, capture_outer) in [
        ("my value = \\x -> \\x -> x", false),
        ("my value x = \\y -> x", true),
    ] {
        let module = lower(text);
        let source = source(&module);
        let LocalSourceForm::Lambda {
            parameter: outer,
            body,
        } = &source.expression(source.body()).unwrap().form
        else {
            panic!("outer");
        };
        let LocalSourceForm::Lambda {
            parameter: inner,
            body,
        } = &source.expression(body).unwrap().form
        else {
            panic!("inner");
        };
        assert_ne!(outer.id, inner.id);
        let expected = if capture_outer { &outer.id } else { &inner.id };
        assert!(matches!(&source.expression(body).unwrap().form,
            LocalSourceForm::Name { resolution: LocalSourceResolution::Parameter(id), .. } if id == expected));
        assert_eq!(source.named_groups().len(), usize::from(capture_outer));
    }
}

#[test]
fn captures_locals_and_restores_sibling_and_final_scopes() {
    let module = lower("my value x = { my y = 1; my f = \\x -> y; x }");
    let source = source(&module);
    let y = &source.bindings()[0].id;
    assert!(source.expressions().iter().any(|expr| matches!(&expr.form,
        LocalSourceForm::Name { resolution: LocalSourceResolution::Local(id), .. } if id == y)));
    let LocalSourceForm::Lambda {
        parameter: outer,
        body,
    } = &source.expression(source.body()).unwrap().form
    else {
        panic!("root");
    };
    let LocalSourceForm::Block {
        final_expression, ..
    } = &source.expression(body).unwrap().form
    else {
        panic!("block");
    };
    assert!(matches!(&source.expression(final_expression).unwrap().form,
        LocalSourceForm::Name { resolution: LocalSourceResolution::Parameter(id), .. } if id == &outer.id));
    let module = lower("my value x = if true: (\\x -> x) else: x");
    let source = self::source(&module);
    let LocalSourceForm::Lambda { parameter, body } =
        &source.expression(source.body()).unwrap().form
    else {
        panic!("root");
    };
    let LocalSourceForm::If { else_branch, .. } = &source.expression(body).unwrap().form else {
        panic!("if");
    };
    assert!(
        matches!(&source.expression(else_branch.as_ref().unwrap()).unwrap().form,
        LocalSourceForm::Name { resolution: LocalSourceResolution::Parameter(id), .. } if id == &parameter.id)
    );
    let module = lower("my value x = (\\x -> x) x");
    let source = self::source(&module);
    let LocalSourceForm::Lambda { parameter, body } =
        &source.expression(source.body()).unwrap().form
    else {
        panic!("root");
    };
    let LocalSourceForm::Apply { argument, .. } = &source.expression(body).unwrap().form else {
        panic!("application");
    };
    assert!(matches!(&source.expression(argument).unwrap().form,
        LocalSourceForm::Name { resolution: LocalSourceResolution::Parameter(id), .. } if id == &parameter.id));
}

#[test]
fn application_and_group_literals_preserve_named_inventory_and_unique_parameters() {
    for text in [
        "my value f = f \\x -> x",
        "my value f = f(\\x -> x)",
        "my value f = (\\x -> x)",
    ] {
        let module = lower(text);
        let source = source(&module);
        assert_eq!(source.named_groups().len(), 1);
        assert_eq!(source.named_groups()[0].formals.len(), 1);
        let parameters: HashSet<_> = source
            .expressions()
            .iter()
            .filter_map(|expr| match &expr.form {
                LocalSourceForm::Lambda { parameter, .. } => Some(parameter.id.clone()),
                _ => None,
            })
            .collect();
        assert_eq!(parameters.len(), 2);
        assert!(
            source
                .expressions()
                .iter()
                .all(|expr| expr.named_group == Some(source.named_groups()[0].id.clone()))
        );
    }
    let module = lower("my value root = { my named x = \\y -> x; \\z -> root }");
    let source = source(&module);
    assert_eq!(source.named_groups().len(), 2);
    let parameters: Vec<_> = source
        .expressions()
        .iter()
        .filter_map(|expr| match &expr.form {
            LocalSourceForm::Lambda { parameter, .. } => Some(&parameter.id),
            _ => None,
        })
        .collect();
    assert_eq!(parameters.len(), 4);
    assert_eq!(parameters.iter().copied().collect::<HashSet<_>>().len(), 4);
}

#[test]
fn typed_origins_join_exact_tokens_and_preserve_pattern_accessor() {
    let text = "my value outer = \\変数 -> outer";
    let parse = parsed(text);
    let module = lower_parse(&parse).unwrap();
    let artifact = ShadowArtifact::from_parsed(parse.clone()).unwrap();
    let foreign_module = lower_parse(&parse).unwrap();
    let foreign_artifact = ShadowArtifact::from_parsed(parsed(text)).unwrap();
    let source = source(&module);
    for expr in source.expressions() {
        let LocalSourceForm::Lambda { parameter, .. } = &expr.form else {
            continue;
        };
        let origin = artifact
            .parameter_source_origin(&module, &parameter.id)
            .unwrap();
        match origin {
            ParameterSourceOrigin::IdentifierPattern(position) => {
                assert_eq!(
                    artifact
                        .parameter_source_position(&module, &parameter.id)
                        .unwrap(),
                    position
                );
                assert_eq!(
                    artifact.position(&position).unwrap().kind(),
                    SyntaxKind::IdentifierPattern
                );
                assert_eq!(
                    artifact.position(&position).unwrap().range(),
                    &parameter.range
                );
            }
            ParameterSourceOrigin::InlineLambda { lambda, binder } => {
                assert_eq!(artifact.source_position(&parameter.source).unwrap(), lambda);
                assert_eq!(
                    artifact.position(&lambda).unwrap().kind(),
                    SyntaxKind::LambdaExpression
                );
                let token = artifact.position(&binder).unwrap();
                assert!(!token.is_node());
                assert_eq!(token.kind(), SyntaxKind::Identifier);
                assert_eq!(token.range(), &parameter.range);
                assert_eq!(&text[token.range().clone()], "変数");
                assert_eq!(token.parent(), Some(&lambda));
                assert_eq!(
                    artifact.parameter_source_position(&module, &parameter.id),
                    Err(SourceIdentityError::MissingSource)
                );
                assert!(
                    module
                        .shadow_parameter_local_owner(&parameter.id)
                        .unwrap()
                        .is_none()
                );
            }
        }
        assert_eq!(
            artifact.parameter_source_origin(&foreign_module, &parameter.id),
            Err(SourceIdentityError::ForeignHirArtifact)
        );
        assert_eq!(
            foreign_artifact.parameter_source_origin(&module, &parameter.id),
            Err(SourceIdentityError::ForeignParse)
        );
    }
}

#[test]
fn malformed_or_unsupported_literals_refuse_private_formation() {
    for text in [
        "my value = \\x ->",
        "my value = \\x -> (",
        "my value = \\x -> (1, 2)",
        "my value = \\x y -> x",
    ] {
        assert!(
            matches!(
                lower_parse(&parsed(text)),
                Err(HirAvailabilityError::StructuralProjection)
            ),
            "{text}"
        );
    }
}
