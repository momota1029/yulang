//! Parse-owned role declaration identities in the nonshipping HIR sidecar.
use super::*;
use yu_syntax::SourceNodeKey;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SourceRoleId {
    pub module: Arc<ModuleId>,
    pub declaration: SourceNodeKey,
}

#[derive(Clone, Debug)]
pub struct SourceRoleHead {
    pub source: SourceNodeKey,
    pub range: Range<usize>,
    pub text: Box<str>,
    /// The syntactic role head, not a globally resolved role name.
    pub spelling: Box<str>,
}

#[derive(Clone, Debug)]
pub struct SourceRoleBody {
    pub source: SourceNodeKey,
    pub range: Range<usize>,
    pub text: Box<str>,
}

#[derive(Clone, Debug)]
pub struct SourceRoleDeclaration {
    pub id: SourceRoleId,
    pub visibility: HirVisibility,
    pub head: SourceRoleHead,
    pub body: Option<SourceRoleBody>,
    pub range: Range<usize>,
}

fn trivia(kind: SyntaxKind) -> bool {
    matches!(kind, SyntaxKind::Whitespace | SyntaxKind::Newline | SyntaxKind::LineComment | SyntaxKind::BlockComment)
}

fn unsupported() -> HirAvailabilityError {
    HirAvailabilityError::StructuralProjection
}

pub(super) fn declarations(
    root: &SyntaxNode,
    module: &ModuleId,
    counters: &LoweringCounters,
) -> Result<Vec<SourceRoleDeclaration>, HirAvailabilityError> {
    let mut result = Vec::new();
    for node in root.children().filter(|node| node.kind() == SyntaxKind::RoleDeclaration) {
        if has_recovery(&node) {
            return Err(unsupported());
        }
        let mut parts = node.children_with_tokens().filter(|part| !trivia(part.kind()));
        let first = parts.next().ok_or_else(unsupported)?;
        let visibility = match first.kind() {
            SyntaxKind::MyKw => {
                if parts.next().is_none_or(|part| part.kind() != SyntaxKind::RoleKw) { return Err(unsupported()); }
                HirVisibility::Private
            }
            SyntaxKind::OurKw => {
                if parts.next().is_none_or(|part| part.kind() != SyntaxKind::RoleKw) { return Err(unsupported()); }
                HirVisibility::Our
            }
            SyntaxKind::PubKw => {
                if parts.next().is_none_or(|part| part.kind() != SyntaxKind::RoleKw) { return Err(unsupported()); }
                HirVisibility::Public
            }
            SyntaxKind::RoleKw => HirVisibility::Our,
            _ => return Err(unsupported()),
        };
        let head = parts.next().and_then(|part| part.into_node())
            .filter(|part| part.kind() == SyntaxKind::TypeExpression)
            .ok_or_else(unsupported)?;
        let spelling = head.children_with_tokens().find_map(|part| {
            (part.kind() == SyntaxKind::Identifier).then(|| part.to_string())
        }).ok_or_else(unsupported)?;
        let body = match (parts.next(), parts.next(), parts.next()) {
            (None, None, None) => None,
            (Some(marker), Some(body), None)
                if marker.kind() == SyntaxKind::Colon
                    && body.kind() == SyntaxKind::IndentedStatementBlock => {
                let body = body.into_node().ok_or_else(unsupported)?;
                Some(SourceRoleBody {
                    source: counters.source_nodes.get(&body).cloned().ok_or_else(unsupported)?,
                    range: crate::range_of(&body),
                    text: body.text().to_string().into_boxed_str(),
                })
            }
            (Some(body), None, None) if body.kind() == SyntaxKind::BracedStatementBlockExpression => {
                let body = body.into_node().ok_or_else(unsupported)?;
                Some(SourceRoleBody {
                    source: counters.source_nodes.get(&body).cloned().ok_or_else(unsupported)?,
                    range: crate::range_of(&body),
                    text: body.text().to_string().into_boxed_str(),
                })
            }
            (Some(semicolon), None, None) if semicolon.kind() == SyntaxKind::Semicolon => None,
            _ => return Err(unsupported()),
        };
        let declaration = counters.source_nodes.get(&node).cloned().ok_or_else(unsupported)?;
        let head_source = counters.source_nodes.get(&head).cloned().ok_or_else(unsupported)?;
        result.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        result.push(SourceRoleDeclaration {
            id: SourceRoleId { module: Arc::new(module.clone()), declaration },
            visibility,
            head: SourceRoleHead {
                source: head_source,
                range: crate::range_of(&head),
                text: head.text().to_string().into_boxed_str(),
                spelling: spelling.into_boxed_str(),
            },
            body,
            range: crate::range_of(&node),
        });
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn role_identity_uses_module_and_exact_parse_occurrence() {
        let text = "role Pick 'container 'key:\n    type value\n    our container.pick: 'key -> value\nrole Pick 'container:\n    our value: 'container -> str";
        let source: Arc<yu_syntax::SourceText> = Arc::from(text);
        let parsed = yu_syntax::parse_file(
            source.clone(),
            Arc::new(yu_syntax::scan_header(source)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        let module_identity = ModuleIdentity::source_root(FileId::new(FileKey::new(
            "role-identity", "roles.yu",
        )));
        let hir = super::super::lower_module_with_local_source(
            module_identity.clone(), &parsed, SemanticImports::empty(),
        ).expect("role sources remain available beside unsupported semantic items");
        let roles = hir.source_role_declarations();
        assert_eq!(roles.len(), 2);
        assert_eq!(roles[0].id.module.as_ref(), module_identity.module());
        assert_eq!(roles[0].head.spelling.as_ref(), "Pick");
        assert_eq!(roles[0].head.text.trim(), "Pick 'container 'key");
        assert_eq!(roles[1].head.text.trim(), "Pick 'container");
        assert_ne!(roles[0].id, roles[1].id, "equal spellings remain distinct source roles");
        assert_eq!(&text[roles[0].range.clone()], "role Pick 'container 'key:\n    type value\n    our container.pick: 'key -> value");
        let first_body = roles[0].body.as_ref().expect("role body");
        assert_eq!(&text[first_body.range.clone()], first_body.text.as_ref());
        assert_ne!(roles[0].head.source, first_body.source);
    }
}
