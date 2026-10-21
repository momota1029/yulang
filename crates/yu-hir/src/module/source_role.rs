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
    pub recovered: bool,
    /// The syntactic role head, not a globally resolved role name.
    pub spelling: Box<str>,
}

#[derive(Clone, Debug)]
pub struct SourceRoleBody {
    pub source: SourceNodeKey,
    pub range: Range<usize>,
    pub text: Box<str>,
    pub recovered: bool,
    pub members: Vec<SourceRoleMember>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SourceRoleMemberId {
    pub role: SourceRoleId,
    pub declaration: SourceNodeKey,
}

#[derive(Clone, Debug)]
pub struct SourceRoleMember {
    pub id: SourceRoleMemberId,
    pub kind: SyntaxKind,
    pub range: Range<usize>,
    pub text: Box<str>,
    pub recovered: bool,
}

#[derive(Clone, Debug)]
pub struct SourceRoleDeclaration {
    pub id: SourceRoleId,
    pub visibility: HirVisibility,
    pub head: SourceRoleHead,
    pub body: Option<SourceRoleBody>,
    pub range: Range<usize>,
    pub recovered: bool,
}

fn trivia(kind: SyntaxKind) -> bool {
    matches!(kind, SyntaxKind::Whitespace | SyntaxKind::Newline | SyntaxKind::LineComment | SyntaxKind::BlockComment)
}

fn unsupported() -> HirAvailabilityError {
    HirAvailabilityError::StructuralProjection
}

fn body_members(
    body: &SyntaxNode,
    role: &SourceRoleId,
    counters: &LoweringCounters,
) -> Result<Vec<SourceRoleMember>, HirAvailabilityError> {
    let mut members = Vec::new();
    for child in body.children() {
        if child.kind() == SyntaxKind::BlockStatementSeparator {
            if child.children().next().is_some() { return Err(unsupported()); }
            continue;
        }
        if child.kind() != SyntaxKind::Statement { return Err(unsupported()); }
        let mut declarations = child.children();
        let declaration = declarations.next().ok_or_else(unsupported)?;
        if declarations.next().is_some() { return Err(unsupported()); }
        members.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        members.push(SourceRoleMember {
            id: SourceRoleMemberId {
                role: role.clone(),
                declaration: counters.source_nodes.get(&declaration).cloned().ok_or_else(unsupported)?,
            },
            kind: declaration.kind(),
            range: crate::range_of(&declaration),
            text: declaration.text().to_string().into_boxed_str(),
            recovered: has_recovery(&declaration),
        });
    }
    Ok(members)
}

pub(super) fn declarations(
    root: &SyntaxNode,
    module: &ModuleId,
    counters: &LoweringCounters,
) -> Result<Vec<SourceRoleDeclaration>, HirAvailabilityError> {
    let mut result = Vec::new();
    for node in root.children().filter(|node| node.kind() == SyntaxKind::RoleDeclaration) {
        let recovered = has_recovery(&node);
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
        let declaration = counters.source_nodes.get(&node).cloned().ok_or_else(unsupported)?;
        let id = SourceRoleId { module: Arc::new(module.clone()), declaration };
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
                    recovered: has_recovery(&body),
                    members: body_members(&body, &id, counters)?,
                })
            }
            (Some(body), None, None) if body.kind() == SyntaxKind::BracedStatementBlockExpression => {
                let body = body.into_node().ok_or_else(unsupported)?;
                Some(SourceRoleBody {
                    source: counters.source_nodes.get(&body).cloned().ok_or_else(unsupported)?,
                    range: crate::range_of(&body),
                    text: body.text().to_string().into_boxed_str(),
                    recovered: has_recovery(&body),
                    members: body_members(&body, &id, counters)?,
                })
            }
            (Some(semicolon), None, None) if semicolon.kind() == SyntaxKind::Semicolon => None,
            _ => return Err(unsupported()),
        };
        let head_source = counters.source_nodes.get(&head).cloned().ok_or_else(unsupported)?;
        result.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        result.push(SourceRoleDeclaration {
            id,
            visibility,
            head: SourceRoleHead {
                source: head_source,
                range: crate::range_of(&head),
                text: head.text().to_string().into_boxed_str(),
                spelling: spelling.into_boxed_str(),
                recovered: has_recovery(&head),
            },
            body,
            range: crate::range_of(&node),
            recovered,
        });
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn role_identity_uses_module_and_exact_parse_occurrence() {
        let text = "role Pick 'container 'key:\n    our value: 'container -> 'key\nrole Pick 'container:\n    our value: 'container -> str";
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
        let members = &roles[0].body.as_ref().expect("role body").members;
        assert_eq!(members.len(), 1);
        assert_eq!(members[0].kind, SyntaxKind::BindingStatement);
        assert_eq!(members[0].id.role, roles[0].id);
        let second_member = &roles[1].body.as_ref().expect("second role body").members[0];
        assert_eq!(second_member.text.split(':').next().unwrap().trim(), "our value");
        assert_ne!(members[0].id, second_member.id, "equal member spellings in separate roles remain distinct");
        assert_eq!(hir.source_role_member(&members[0].id).unwrap().unwrap().id, members[0].id);
        assert_eq!(hir.source_role_member(&second_member.id).unwrap().unwrap().id, second_member.id);
        for member in members {
            assert_eq!(&text[member.range.clone()], member.text.as_ref());
        }
        assert_eq!(&text[roles[0].range.clone()], "role Pick 'container 'key:\n    our value: 'container -> 'key");
        let first_body = roles[0].body.as_ref().expect("role body");
        assert_eq!(&text[first_body.range.clone()], first_body.text.as_ref());
        assert_ne!(roles[0].head.source, first_body.source);
    }
}
