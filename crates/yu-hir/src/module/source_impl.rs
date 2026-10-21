//! Parse-owned source identities for standalone implementation declarations.
use super::*;
use yu_syntax::SourceNodeKey;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SourceImplementationId {
    pub module: Arc<ModuleId>,
    pub declaration: SourceNodeKey,
}

#[derive(Clone, Debug)]
pub struct SourceImplementationType {
    pub source: SourceNodeKey,
    pub range: Range<usize>,
    pub text: Box<str>,
}

#[derive(Clone, Debug)]
pub struct SourceImplementationBodyEntry {
    /// A member declaration node or a declaration-owned where-clause node.
    pub source: SourceNodeKey,
    pub member: Option<SourceImplementationMemberId>,
    pub kind: SyntaxKind,
    pub range: Range<usize>,
    pub text: Box<str>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SourceImplementationMemberId {
    pub implementation: SourceImplementationId,
    pub declaration: SourceNodeKey,
}

#[derive(Clone, Debug)]
pub struct SourceImplementationBody {
    pub source: SourceNodeKey,
    pub range: Range<usize>,
    pub text: Box<str>,
    pub entries: Vec<SourceImplementationBodyEntry>,
}

#[derive(Clone, Debug)]
pub struct SourceImplementationDeclaration {
    pub id: SourceImplementationId,
    /// Syntactic receiver/input head, not an inferred or normalized type.
    pub target: SourceImplementationType,
    /// Syntactic role application, not a resolved role identity.
    pub role: SourceImplementationType,
    pub body: Option<SourceImplementationBody>,
    pub range: Range<usize>,
}

fn unavailable() -> HirAvailabilityError {
    HirAvailabilityError::StructuralProjection
}

fn source_type(
    node: &SyntaxNode,
    counters: &LoweringCounters,
) -> Result<SourceImplementationType, HirAvailabilityError> {
    Ok(SourceImplementationType {
        source: counters
            .source_nodes
            .get(node)
            .cloned()
            .ok_or_else(unavailable)?,
        range: crate::range_of(node),
        text: node.text().to_string().into_boxed_str(),
    })
}

fn body_entries(
    body: &SyntaxNode,
    implementation: &SourceImplementationId,
    counters: &LoweringCounters,
) -> Result<Vec<SourceImplementationBodyEntry>, HirAvailabilityError> {
    let mut entries = Vec::new();
    for child in body.children() {
        let (node, is_member) = match child.kind() {
            SyntaxKind::BlockStatementSeparator => {
                if child.children().next().is_some() {
                    return Err(unavailable());
                }
                continue;
            }
            SyntaxKind::WhereClause => {
                if has_recovery(&child) {
                    return Err(unavailable());
                }
                (child, false)
            }
            SyntaxKind::Statement => {
                let mut declarations = child.children();
                let declaration = declarations.next().ok_or_else(unavailable)?;
                if declarations.next().is_some() || has_recovery(&declaration) {
                    return Err(unavailable());
                }
                (declaration, true)
            }
            _ => return Err(unavailable()),
        };
        entries
            .try_reserve(1)
            .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        let source = counters
            .source_nodes
            .get(&node)
            .cloned()
            .ok_or_else(unavailable)?;
        entries.push(SourceImplementationBodyEntry {
            source: source.clone(),
            member: is_member.then(|| SourceImplementationMemberId {
                implementation: implementation.clone(),
                declaration: source,
            }),
            kind: node.kind(),
            range: crate::range_of(&node),
            text: node.text().to_string().into_boxed_str(),
        });
    }
    Ok(entries)
}

pub(super) fn declarations(
    root: &SyntaxNode,
    module: &ModuleId,
    counters: &LoweringCounters,
) -> Result<Vec<SourceImplementationDeclaration>, HirAvailabilityError> {
    let mut result = Vec::new();
    for node in root
        .children()
        .filter(|node| node.kind() == SyntaxKind::ImplDeclaration)
    {
        if has_recovery(&node) {
            return Err(unavailable());
        }
        let mut target = None;
        let mut role = None;
        let mut description_seen = false;
        let mut body = None;
        for child in node.children() {
            match child.kind() {
                SyntaxKind::TypeExpression if !description_seen && target.is_none() => {
                    target = Some(source_type(&child, counters)?);
                }
                SyntaxKind::ImplDescription if !description_seen => {
                    description_seen = true;
                    let mut role_types = child
                        .children()
                        .filter(|part| part.kind() == SyntaxKind::TypeExpression);
                    let role_node = role_types.next().ok_or_else(unavailable)?;
                    if role_types.next().is_some() || has_recovery(&child) {
                        return Err(unavailable());
                    }
                    role = Some(source_type(&role_node, counters)?);
                }
                SyntaxKind::IndentedStatementBlock | SyntaxKind::BracedStatementBlockExpression
                    if body.is_none() =>
                {
                    body = Some(child);
                }
                SyntaxKind::Error | SyntaxKind::Missing | SyntaxKind::Invalid => {
                    return Err(unavailable());
                }
                _ => {}
            }
        }
        let target = target.ok_or_else(unavailable)?;
        let role = role.ok_or_else(unavailable)?;
        let declaration = counters
            .source_nodes
            .get(&node)
            .cloned()
            .ok_or_else(unavailable)?;
        let id = SourceImplementationId {
            module: Arc::new(module.clone()),
            declaration,
        };
        let body = if let Some(body) = body {
            Some(SourceImplementationBody {
                source: counters
                    .source_nodes
                    .get(&body)
                    .cloned()
                    .ok_or_else(unavailable)?,
                range: crate::range_of(&body),
                text: body.text().to_string().into_boxed_str(),
                entries: body_entries(&body, &id, counters)?,
            })
        } else {
            None
        };
        result
            .try_reserve(1)
            .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        result.push(SourceImplementationDeclaration {
            id,
            target,
            role,
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
    fn implementation_identity_retains_target_role_and_ordered_body_owners() {
        let text = "impl int: Display:\n    where 'a: Display\n    our value.show = \"x\"\nimpl int: Display;";
        let source: Arc<yu_syntax::SourceText> = Arc::from(text);
        let parsed = yu_syntax::parse_file(
            source.clone(),
            Arc::new(yu_syntax::scan_header(source)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        let module_identity =
            ModuleIdentity::source_root(FileId::new(FileKey::new("impl-identity", "impls.yu")));
        let hir = super::super::lower_module_with_local_source(
            module_identity.clone(),
            &parsed,
            SemanticImports::empty(),
        )
        .expect("implementation sources remain available beside unsupported semantic items");
        let implementations = hir.source_implementation_declarations();
        assert_eq!(implementations.len(), 2);
        assert!(
            implementations
                .iter()
                .all(|item| item.id.module.as_ref() == module_identity.module())
        );
        assert_ne!(implementations[0].id, implementations[1].id);
        assert_eq!(implementations[0].target.text.trim(), "int");
        assert_eq!(implementations[0].role.text.trim(), "Display");
        assert_eq!(
            &text[implementations[0].target.range.clone()],
            implementations[0].target.text.as_ref()
        );
        assert_eq!(
            &text[implementations[0].role.range.clone()],
            implementations[0].role.text.as_ref()
        );
        let body = implementations[0]
            .body
            .as_ref()
            .expect("implementation body");
        assert_eq!(body.entries.len(), 2);
        assert_eq!(body.entries[0].kind, SyntaxKind::WhereClause);
        assert_eq!(body.entries[1].kind, SyntaxKind::BindingStatement);
        assert!(body.entries[0].member.is_none());
        assert_eq!(
            body.entries[1].member.as_ref().unwrap().implementation,
            implementations[0].id
        );
        for entry in &body.entries {
            assert_eq!(&text[entry.range.clone()], entry.text.as_ref());
        }
        assert!(implementations[1].body.is_none());
    }
}
