//! Parse-owned source identities for standalone implementation declarations.
use super::*;
use yu_syntax::SourceNodeKey;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SourceImplementationId {
    pub module: Arc<ModuleId>,
    pub declaration: SourceNodeKey,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceImplementationType {
    pub source: SourceNodeKey,
    pub range: Range<usize>,
    pub text: Box<str>,
    pub recovered: bool,
    /// A bounded structural view for the simple and tuple target forms used
    /// by source-directed implementation matching. `None` means the syntax
    /// remains retained as text but is outside this matcher fragment.
    pub shape: Option<SourceImplementationTypeShape>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SourceImplementationTypeShape {
    Name(Box<str>),
    Tuple(Vec<SourceImplementationTypeShape>),
    /// Prefix type application such as `list 'a` or `result 'ok 'err`.
    /// The first element is the constructor and the rest are arguments.
    Apply(Vec<SourceImplementationTypeShape>),
}

impl SourceImplementationTypeShape {
    pub fn retained_bytes(&self) -> usize {
        match self {
            Self::Name(name) => name.len(),
            Self::Tuple(items) => items.capacity()
                .checked_mul(std::mem::size_of::<Self>())
                .and_then(|bytes| items.iter().try_fold(bytes, |total, item|
                    total.checked_add(item.retained_bytes())))
                .expect("implementation type shape accounting fits usize"),
            Self::Apply(items) => items.capacity()
                .checked_mul(std::mem::size_of::<Self>())
                .and_then(|bytes| items.iter().try_fold(bytes, |total, item|
                    total.checked_add(item.retained_bytes())))
                .expect("implementation type application accounting fits usize"),
        }
    }

    /// Structurally matches an implementation target against a concrete
    /// receiver shape, returning the source type-variable substitution.
    /// Unsupported syntax has no shape and cannot enter this relation.
    pub fn match_target(
        &self,
        actual: &Self,
    ) -> Option<std::collections::HashMap<Box<str>, Self>> {
        fn go(
            pattern: &SourceImplementationTypeShape,
            actual: &SourceImplementationTypeShape,
            variables: &mut std::collections::HashMap<Box<str>, SourceImplementationTypeShape>,
        ) -> Option<()> {
            match (pattern, actual) {
                (SourceImplementationTypeShape::Name(name), actual) if name.starts_with('\'') => {
                    if let Some(previous) = variables.get(name.as_ref()) {
                        return (previous == actual).then_some(());
                    }
                    variables.try_reserve(1).ok()?;
                    variables.insert(name.clone(), actual.clone());
                    Some(())
                }
                (SourceImplementationTypeShape::Name(left), SourceImplementationTypeShape::Name(right)) => {
                    (left == right).then_some(())
                }
                (SourceImplementationTypeShape::Tuple(left), SourceImplementationTypeShape::Tuple(right))
                    if left.len() == right.len() => {
                    for (left, right) in left.iter().zip(right) { go(left, right, variables)?; }
                    Some(())
                }
                (SourceImplementationTypeShape::Apply(left), SourceImplementationTypeShape::Apply(right))
                    if left.len() == right.len() && left.len() >= 2 => {
                    for (left, right) in left.iter().zip(right) { go(left, right, variables)?; }
                    Some(())
                }
                _ => None,
            }
        }
        let mut variables = std::collections::HashMap::new();
        go(self, actual, &mut variables)?;
        Some(variables)
    }
}

#[derive(Clone, Debug)]
pub struct SourceImplementationBodyEntry {
    /// A member declaration node or a declaration-owned where-clause node.
    pub source: SourceNodeKey,
    pub member: Option<SourceImplementationMemberId>,
    pub kind: SyntaxKind,
    pub range: Range<usize>,
    pub text: Box<str>,
    pub recovered: bool,
    pub header: Option<SourceMemberHeader>,
    /// Structured subject and role for the implementation's parsed where
    /// prerequisite. Unsupported clause forms remain source-owned as text and
    /// have no matcher projection.
    pub where_clause: Option<SourceImplementationWhereClause>,
    pub(crate) source_path: Option<Box<[u32]>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceImplementationWhereClause {
    pub subject: SourceImplementationType,
    pub role: SourceImplementationType,
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
    pub recovered: bool,
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
    pub recovered: bool,
}

fn unavailable() -> HirAvailabilityError {
    HirAvailabilityError::StructuralProjection
}

fn source_type(
    node: &SyntaxNode,
    counters: &LoweringCounters,
) -> Result<SourceImplementationType, HirAvailabilityError> {
    let text = node.text().to_string();
    Ok(SourceImplementationType {
        source: counters
            .source_nodes
            .get(node)
            .cloned()
            .ok_or_else(unavailable)?,
        range: crate::range_of(node),
        shape: implementation_type_shape(&text, 0),
        text: text.into_boxed_str(),
        recovered: has_recovery(node),
    })
}

fn implementation_type_shape(text: &str, depth: usize) -> Option<SourceImplementationTypeShape> {
    if depth >= 128 { return None; }
    let text = text.trim();
    if text.is_empty() { return None; }
    if text.starts_with('(') && text.ends_with(')') {
        let inner = &text[1..text.len() - 1];
        if inner.trim().is_empty() {
            return Some(SourceImplementationTypeShape::Tuple(Vec::new()));
        }
        let mut nesting = 0usize;
        let mut start = 0usize;
        let mut parts = Vec::new();
        let mut tuple = false;
        for (offset, character) in inner.char_indices() {
            match character {
                '(' => nesting = nesting.checked_add(1)?,
                ')' => nesting = nesting.checked_sub(1)?,
                ',' if nesting == 0 => {
                    tuple = true;
                    let part = inner[start..offset].trim();
                    if !part.is_empty() {
                        parts.try_reserve(1).ok()?;
                        parts.push(implementation_type_shape(part, depth + 1)?);
                    }
                    start = offset + character.len_utf8();
                }
                _ => {}
            }
        }
        if nesting != 0 { return None; }
        if tuple {
            let last = inner[start..].trim();
            if !last.is_empty() {
                parts.try_reserve(1).ok()?;
                parts.push(implementation_type_shape(last, depth + 1)?);
            }
            return Some(SourceImplementationTypeShape::Tuple(parts));
        }
        return implementation_type_shape(inner, depth + 1);
    }
    let mut ranges = Vec::new();
    let mut nesting = 0usize;
    let mut start = None;
    for (offset, character) in text.char_indices() {
        match character {
            '(' => {
                if nesting == 0 && start.is_none() { start = Some(offset); }
                nesting = nesting.checked_add(1)?;
            }
            ')' => nesting = nesting.checked_sub(1)?,
            character if character.is_whitespace() && nesting == 0 => {
                if let Some(part_start) = start.take() {
                    ranges.try_reserve(1).ok()?;
                    ranges.push(part_start..offset);
                }
            }
            _ => if start.is_none() { start = Some(offset); },
        }
    }
    if nesting != 0 { return None; }
    if let Some(part_start) = start {
        ranges.try_reserve(1).ok()?;
        ranges.push(part_start..text.len());
    }
    if ranges.len() > 1 {
        let mut parts = Vec::new();
        parts.try_reserve_exact(ranges.len()).ok()?;
        for range in ranges { parts.push(implementation_type_shape(&text[range], depth + 1)?); }
        return Some(SourceImplementationTypeShape::Apply(parts));
    }
    implementation_type_name(text)
        .then(|| SourceImplementationTypeShape::Name(text.to_owned().into_boxed_str()))
}

fn implementation_type_name(text: &str) -> bool {
    let name = text.strip_prefix('\'').unwrap_or(text);
    if name.is_empty() { return false; }
    name.split("::").all(|part| {
        let mut characters = part.chars();
        characters.next().is_some_and(|first| first == '_' || first.is_alphabetic())
            && characters.all(|character| character == '_' || character.is_alphanumeric())
    })
}

fn body_entries(
    body: &SyntaxNode,
    implementation: &SourceImplementationId,
    root: &SyntaxNode,
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
                (child, false)
            }
            SyntaxKind::Statement => {
                let mut declarations = child.children();
                let declaration = declarations.next().ok_or_else(unavailable)?;
                if declarations.next().is_some() {
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
        let where_clause = (!is_member).then(|| implementation_where_clause(&node, counters)).flatten();
        entries.push(SourceImplementationBodyEntry {
            source: source.clone(),
            member: is_member.then(|| SourceImplementationMemberId {
                implementation: implementation.clone(),
                declaration: source,
            }),
            kind: node.kind(),
            range: crate::range_of(&node),
            text: node.text().to_string().into_boxed_str(),
            recovered: has_recovery(&node),
            header: if is_member { local_source::member_header(&node, counters)? } else { None },
            where_clause,
            source_path: is_member.then(|| crate::source_identity::source_path(root, &node))
                .transpose()?,
        });
    }
    Ok(entries)
}

fn implementation_where_clause(
    node: &SyntaxNode,
    counters: &LoweringCounters,
) -> Option<SourceImplementationWhereClause> {
    let mut parts = node.children_with_tokens().filter(|element| !matches!(
        element.kind(), SyntaxKind::Whitespace | SyntaxKind::Newline
            | SyntaxKind::LineComment | SyntaxKind::BlockComment,
    ));
    if parts.next()?.kind() != SyntaxKind::WhereKw { return None; }
    let subject = parts.next()?.into_node().filter(|node| node.kind() == SyntaxKind::TypeExpression)?;
    if parts.next()?.kind() != SyntaxKind::Colon { return None; }
    let role = parts.next()?.into_node().filter(|node| node.kind() == SyntaxKind::TypeExpression)?;
    if parts.next().is_some() { return None; }
    Some(SourceImplementationWhereClause {
        subject: source_type(&subject, counters).ok()?,
        role: source_type(&role, counters).ok()?,
    })
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
        let recovered = has_recovery(&node);
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
                    if role_types.next().is_some() {
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
                recovered: has_recovery(&body),
                entries: body_entries(&body, &id, root, counters)?,
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
            recovered,
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
        assert!(body.entries[0].source_path.is_none(), "where clause is not a member body");
        assert_eq!(
            body.entries[1].member.as_ref().unwrap().implementation,
            implementations[0].id
        );
        let member_id = body.entries[1].member.as_ref().unwrap();
        assert_eq!(hir.source_implementation_member(member_id).unwrap().unwrap().member.as_ref(), Some(member_id));
        let member_root = hir.source_implementation_member_root(member_id).unwrap().unwrap();
        assert!(matches!(member_root, SourceRootId::Member(ref root) if root.kind() == SourceMemberKind::Implementation));
        assert!(hir.owns_source_root(&member_root));
        let member_node = hir.source_implementation_member_node(member_id).unwrap().unwrap();
        assert_eq!(member_node.kind(), body.entries[1].kind);
        assert_eq!(member_node.text().to_string(), body.entries[1].text.as_ref());
        assert_eq!(crate::range_of(&member_node), body.entries[1].range);
        assert!(parsed.owns_source_key(&member_id.declaration));
        let foreign_member = SourceImplementationMemberId {
            implementation: implementations[1].id.clone(),
            declaration: member_id.declaration.clone(),
        };
        assert!(hir.source_implementation_member(&foreign_member).unwrap().is_none());
        for entry in &body.entries {
            assert_eq!(&text[entry.range.clone()], entry.text.as_ref());
        }
        assert!(implementations[1].body.is_none());
    }

    #[test]
    fn implementation_target_retains_bounded_tuple_shape() {
        let text = "impl ('a, ('b, int)): Display:\n    our value.show = value";
        let source: Arc<yu_syntax::SourceText> = Arc::from(text);
        let parsed = yu_syntax::parse_file(
            source.clone(),
            Arc::new(yu_syntax::scan_header(source)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        let identity = ModuleIdentity::source_root(FileId::new(FileKey::new(
            "impl-tuple-shape", "impls.yu",
        )));
        let hir = super::super::lower_module_with_local_source(
            identity, &parsed, SemanticImports::empty(),
        ).unwrap();
        let implementations = hir.source_implementation_declarations();
        let [implementation] = implementations else {
            panic!("one implementation declaration")
        };
        assert_eq!(implementation.target.text.trim(), "('a, ('b, int))");
        assert_eq!(implementation.target.shape, Some(SourceImplementationTypeShape::Tuple(vec![
            SourceImplementationTypeShape::Name("'a".into()),
            SourceImplementationTypeShape::Tuple(vec![
                SourceImplementationTypeShape::Name("'b".into()),
                SourceImplementationTypeShape::Name("int".into()),
            ]),
        ])));
        let target = implementation.target.shape.as_ref().unwrap();
        let actual = SourceImplementationTypeShape::Tuple(vec![
            SourceImplementationTypeShape::Name("str".into()),
            SourceImplementationTypeShape::Tuple(vec![
                SourceImplementationTypeShape::Name("bool".into()),
                SourceImplementationTypeShape::Name("int".into()),
            ]),
        ]);
        let variables = target.match_target(&actual).unwrap();
        assert_eq!(variables.get("'a"), Some(&SourceImplementationTypeShape::Name("str".into())));
        assert_eq!(variables.get("'b"), Some(&SourceImplementationTypeShape::Name("bool".into())));
        assert!(target.match_target(&SourceImplementationTypeShape::Tuple(vec![
            SourceImplementationTypeShape::Name("str".into()),
        ])).is_none(), "tuple arity is part of applicability");
    }

    #[test]
    fn implementation_target_retains_prefix_type_applications() {
        let text = "impl (result 'ok (list 'item)): Display:\n    our value.show = value";
        let source: Arc<yu_syntax::SourceText> = Arc::from(text);
        let parsed = yu_syntax::parse_file(
            source.clone(),
            Arc::new(yu_syntax::scan_header(source)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        let hir = super::super::lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new("impl-application-shape", "impls.yu"))),
            &parsed,
            SemanticImports::empty(),
        ).unwrap();
        let [implementation] = hir.source_implementation_declarations() else {
            panic!("one implementation declaration")
        };
        let expected = SourceImplementationTypeShape::Apply(vec![
            SourceImplementationTypeShape::Name("result".into()),
            SourceImplementationTypeShape::Name("'ok".into()),
            SourceImplementationTypeShape::Apply(vec![
                SourceImplementationTypeShape::Name("list".into()),
                SourceImplementationTypeShape::Name("'item".into()),
            ]),
        ]);
        assert_eq!(implementation.target.shape, Some(expected.clone()));
        let actual = SourceImplementationTypeShape::Apply(vec![
            SourceImplementationTypeShape::Name("result".into()),
            SourceImplementationTypeShape::Name("int".into()),
            SourceImplementationTypeShape::Apply(vec![
                SourceImplementationTypeShape::Name("list".into()),
                SourceImplementationTypeShape::Name("str".into()),
            ]),
        ]);
        let mut substitution = expected.match_target(&actual).unwrap();
        assert_eq!(substitution.remove("'ok"), Some(SourceImplementationTypeShape::Name("int".into())));
        assert_eq!(substitution.remove("'item"), Some(SourceImplementationTypeShape::Name("str".into())));
        assert!(expected.match_target(&SourceImplementationTypeShape::Tuple(vec![
            SourceImplementationTypeShape::Name("int".into()),
        ])).is_none(), "an applied constructor cannot match a tuple receiver");
    }
}
