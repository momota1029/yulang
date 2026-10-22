use std::{
    alloc::{Layout, alloc},
    any::Any,
    collections::HashMap,
    hash::{Hash, Hasher},
    ops::Range,
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
};

use yu_syntax::{
    ParsedFile, SourceRevision, StructuralRecovery, StructuralRecoveryKind, SyntaxKind, SyntaxNode,
};

use crate::{AssociationError, AssociationProvenance, HirExpr, associate_chain_owned, associate_chain_owned_with_sources, range_of};

pub(crate) mod local_source;
pub(crate) mod source_annotation;
pub(crate) mod source_exports;
#[cfg(any(feature = "shadow", test))]
pub(crate) mod source_impl;
#[cfg(any(feature = "shadow", test))]
pub(crate) mod source_role;

/// A compiler-supplied, already-normalized file key.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct FileKey {
    realm: Box<str>,
    normalized_workspace_relative_path: Box<str>,
}

impl FileKey {
    pub fn new(
        realm: impl Into<Box<str>>,
        normalized_workspace_relative_path: impl Into<Box<str>>,
    ) -> Self {
        Self {
            realm: realm.into(),
            normalized_workspace_relative_path: normalized_workspace_relative_path.into(),
        }
    }

    pub fn realm(&self) -> &str {
        &self.realm
    }

    pub fn normalized_workspace_relative_path(&self) -> &str {
        &self.normalized_workspace_relative_path
    }
}

/// Collision-safe identity for one compiler-supplied file key.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct FileId(FileKey);

impl FileId {
    pub fn new(key: FileKey) -> Self {
        Self(key)
    }

    pub fn key(&self) -> &FileKey {
        &self.0
    }
}

/// The only module identity supported by this standalone slice.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ModuleId {
    SourceRoot(FileId),
}

impl ModuleId {
    pub fn source_root(file: FileId) -> Self {
        Self::SourceRoot(file)
    }

    pub fn file(&self) -> &FileId {
        match self {
            Self::SourceRoot(file) => file,
        }
    }
}

/// Compiler-owned module identity supplied to HIR lowering.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ModuleIdentity {
    file: FileId,
    module: ModuleId,
}

impl ModuleIdentity {
    pub fn new(file: FileId, module: ModuleId) -> Self {
        Self { file, module }
    }

    pub fn source_root(file: FileId) -> Self {
        Self {
            module: ModuleId::source_root(file.clone()),
            file,
        }
    }

    pub fn file(&self) -> &FileId {
        &self.file
    }

    pub fn module(&self) -> &ModuleId {
        &self.module
    }
}

/// Optional caller-owned context retained for source-bound semantic work.
///
/// This binding records artifact correspondence only. It does not certify any
/// semantic property of the caller payload.
#[derive(Clone)]
pub struct SemanticImports {
    caller_evidence: Option<CallerEvidenceBinding>,
    source_imports: Option<source_exports::SourceImportEnvironment>,
}

fn resolve_implicit_prelude_imports(
    parsed: &ParsedFile,
    identity: &ModuleIdentity,
    indexes: &[source_exports::SourceExportIndex],
) -> Result<(yu_syntax::SourceNodeKey, HashMap<Box<str>, source_exports::SourceImportBinding>), HirAvailabilityError> {
    resolve_implicit_prelude_imports_selected(parsed, identity, indexes, None)
}

fn resolve_implicit_prelude_imports_selected(
    parsed: &ParsedFile,
    identity: &ModuleIdentity,
    indexes: &[source_exports::SourceExportIndex],
    selected_names: Option<&std::collections::BTreeSet<Box<str>>>,
) -> Result<(yu_syntax::SourceNodeKey, HashMap<Box<str>, source_exports::SourceImportBinding>), HirAvailabilityError> {
    if identity.file != *identity.module.file() {
        return Err(HirAvailabilityError::InconsistentIdentity);
    }
    let parse_root = parsed.source_root().key();
    let root = SyntaxNode::new_root(parsed.green().clone());
    let own = index_source_exports(identity.clone(), parsed)?;
    let mut locally_declared = std::collections::BTreeSet::<Box<str>>::new();
    locally_declared.extend(own.declarations.iter().filter_map(|declaration|
        declaration.name.clone()));
    let mut requested = std::collections::BTreeSet::<Box<str>>::new();
    if let Some(selected) = selected_names {
        requested.extend(selected.iter().cloned());
    } else {
        for node in root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::IdentifierExpression)
        {
            if let Some(name) = node
                .children_with_tokens()
                .filter_map(|element| element.into_token())
                .find(|token| token.kind() == SyntaxKind::Identifier)
            {
                requested.insert(name.text().into());
            }
        }
        for clause in root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::WhereClause)
        {
            let mut parts = clause.children_with_tokens().filter(|element| {
                !matches!(
                    element.kind(),
                    SyntaxKind::Whitespace
                        | SyntaxKind::Newline
                        | SyntaxKind::LineComment
                        | SyntaxKind::BlockComment
                )
            });
            let _keyword = parts.next();
            let _subject = parts.next();
            let _colon = parts.next();
            let Some(role) = parts.next().and_then(|element| element.into_node()) else {
                continue;
            };
            if let Some(name) = role
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .find(|token| token.kind() == SyntaxKind::Identifier)
            {
                requested.insert(name.text().into());
            }
        }
    }
    let mut names = HashMap::new();
    names
        .try_reserve(requested.len())
        .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
    for name in requested {
        // Local declarations shadow the implicit prelude. Resolving their
        // spelling through the prelude can fail on an unrelated recovered
        // export even though the source name is already owned by this module.
        if locally_declared.contains(&name) { continue; }
        match source_exports::resolve_public_export(indexes, "std::prelude", &name) {
            Ok(resolution) => {
                names.insert(name, source_exports::SourceImportBinding::Resolved(resolution));
            }
            Err(source_exports::SourceExportResolveError::MissingExport { .. }) => {}
            Err(source_exports::SourceExportResolveError::Ambiguous { .. }) => {
                names.insert(name, source_exports::SourceImportBinding::Ambiguous);
            }
            Err(_) => return Err(HirAvailabilityError::SourceImportResolutionUnavailable),
        }
    }
    Ok((parse_root, names))
}

fn resolve_source_imports(
    parsed: &ParsedFile,
    identity: &ModuleIdentity,
    indexes: &[source_exports::SourceExportIndex],
) -> Result<(yu_syntax::SourceNodeKey, HashMap<Box<str>, source_exports::SourceImportBinding>), HirAvailabilityError> {
    let (parse_root, mut names) = resolve_source_imports_selected(parsed, identity, indexes, None)?;
    // Qualified value uses carry the same exact export identities in a whole
    // consumer as in a projected provider/member body. No spelling alone
    // authorizes an import: the supplied public source indexes resolve it.
    let qualified = selected_member_value_paths(
        parsed, indexes, &std::collections::HashSet::from([parse_root.clone()]),
    )?;
    names.extend(qualified);
    Ok((parse_root, names))
}

fn resolve_source_imports_selected(
    parsed: &ParsedFile,
    identity: &ModuleIdentity,
    indexes: &[source_exports::SourceExportIndex],
    selected_names: Option<&std::collections::BTreeSet<Box<str>>>,
) -> Result<(yu_syntax::SourceNodeKey, HashMap<Box<str>, source_exports::SourceImportBinding>), HirAvailabilityError> {
    use source_exports::{SourceImportBinding, SourceUseSelection};

    if identity.file != *identity.module.file() {
        return Err(HirAvailabilityError::InconsistentIdentity);
    }
    let parse_root = parsed.source_root().key();
    let own = index_source_exports(identity.clone(), parsed)?;
    source_exports::module_label(&identity.module)
        .ok_or(HirAvailabilityError::SourceImportResolutionUnavailable)?;
    let mut names = HashMap::<Box<str>, SourceImportBinding>::new();
    let mut available = std::collections::BTreeSet::<Box<str>>::new();
    for index in indexes {
        for declaration in &index.declarations {
            if declaration.public {
                if let Some(name) = &declaration.name {
                    available.insert(name.clone());
                }
            }
        }
        for declaration in &index.uses {
            if !declaration.public { continue; }
            for leaf in source_exports::flatten_use_declaration(declaration)
                .map_err(|_| HirAvailabilityError::SourceImportResolutionUnavailable)?
            {
                if let source_exports::SourceUseSelection::Name(selected) = leaf.selection {
                    available.insert(leaf.alias.unwrap_or(selected));
                }
            }
        }
    }

    fn merge_import(
        names: &mut HashMap<Box<str>, SourceImportBinding>,
        name: Box<str>,
        binding: SourceImportBinding,
    ) {
        use SourceImportBinding::{Ambiguous, Resolved};
        match names.get(&name) {
            None => { names.insert(name, binding); }
            Some(Resolved(previous)) => match &binding {
                Resolved(next) if previous.identity() == next.identity() => {}
                _ => { names.insert(name, Ambiguous); }
            },
            Some(Ambiguous) => {}
        }
    }
    for declaration in &own.uses {
        let leaves = source_exports::flatten_use_declaration(declaration)
            .map_err(|_| HirAvailabilityError::SourceImportResolutionUnavailable)?;
        for leaf in leaves {
            let (target, selected, exposed) = match leaf.selection {
                SourceUseSelection::Name(selected) => {
                    if leaf.path.len() < 2 { return Err(HirAvailabilityError::SourceImportResolutionUnavailable); }
                    let target = leaf.path[..leaf.path.len() - 1].iter().map(AsRef::as_ref).collect::<Vec<_>>().join("::");
                    let exposed = leaf.alias.unwrap_or_else(|| selected.clone());
                    (target, Some(selected), Some(exposed))
                }
                SourceUseSelection::Glob { exclusions } => {
                    if leaf.path.is_empty() { return Err(HirAvailabilityError::SourceImportResolutionUnavailable); }
                    let excluded = exclusions.into_iter().collect::<std::collections::BTreeSet<_>>();
                    let target = leaf.path.iter().map(AsRef::as_ref).collect::<Vec<_>>().join("::");
                    if selected_names.is_none() {
                        source_exports::validate_public_source_module(indexes, &target)
                            .map_err(|_| HirAvailabilityError::SourceImportResolutionUnavailable)?;
                    }
                    // Resolve only names observed in pinned declaration indexes. A name with
                    // more than one source route remains explicitly ambiguous.
                    for candidate in &available {
                        if !excluded.contains(candidate)
                            && selected_names.is_none_or(|selected| selected.contains(candidate))
                        {
                            let resolved = match source_exports::resolve_public_export(indexes, &target, candidate) {
                                Ok(value) => Some(SourceImportBinding::Resolved(value)),
                                Err(source_exports::SourceExportResolveError::MissingExport { .. }) => None,
                                Err(source_exports::SourceExportResolveError::Ambiguous { .. }) => Some(SourceImportBinding::Ambiguous),
                Err(_) => return Err(HirAvailabilityError::SourceImportResolutionUnavailable),
                            };
                            if let Some(value) = resolved {
                                merge_import(&mut names, candidate.clone(), value);
                            }
                        }
                    }
                    continue;
                }
            };
            let selected = selected.expect("named use has selected name");
            let exposed = exposed.expect("named use has exposed name");
            if selected_names.is_some_and(|names| !names.contains(&exposed)) { continue; }
            let resolved = match source_exports::resolve_public_export(indexes, &target, &selected) {
                Ok(value) => SourceImportBinding::Resolved(value),
                Err(source_exports::SourceExportResolveError::MissingExport { .. }) => return Err(HirAvailabilityError::SourceImportResolutionUnavailable),
                Err(source_exports::SourceExportResolveError::Ambiguous { .. }) => SourceImportBinding::Ambiguous,
                Err(_) => return Err(HirAvailabilityError::SourceImportResolutionUnavailable),
            };
            // Explicit source imports take precedence over the implicit prelude.
            merge_import(&mut names, exposed, resolved);
        }
    }
    // The prelude is implicit in Yulang2 modules. Explicit imports already
    // occupy their local names and therefore shadow the prelude binding.
    let (prelude_root, prelude) = resolve_implicit_prelude_imports_selected(parsed, identity, indexes, selected_names)?;
    debug_assert_eq!(parse_root, prelude_root);
    for (name, binding) in prelude { names.entry(name).or_insert(binding); }
    Ok((parse_root, names))
}

#[cfg(any(feature = "shadow", test))]
fn selected_source_names(
    parsed: &ParsedFile,
    selected_roots: &std::collections::HashSet<yu_syntax::SourceNodeKey>,
) -> Result<std::collections::BTreeSet<Box<str>>, HirAvailabilityError> {
    if selected_roots.iter().any(|root| !parsed.owns_source_key(root)) {
        return Err(HirAvailabilityError::ForeignSourceImport);
    }
    let source_nodes = crate::source_identity::try_source_keys(parsed)?;
    let root = SyntaxNode::new_root(parsed.green().clone());
    let mut found = std::collections::HashSet::new();
    let mut names = std::collections::BTreeSet::new();
    for node in root.descendants() {
        let Some(key) = source_nodes.get(&node) else { continue; };
        if !selected_roots.contains(key) { continue; }
        found.insert(key.clone());
        for occurrence in node.descendants().filter(|child| child.kind() == SyntaxKind::IdentifierExpression) {
            if let Some(name) = occurrence.children_with_tokens()
                .filter_map(|element| element.into_token())
                .find(|token| token.kind() == SyntaxKind::Identifier)
            {
                names.insert(name.text().into());
            }
        }
        for clause in node.descendants().filter(|child| child.kind() == SyntaxKind::WhereClause) {
            let mut parts = clause.children_with_tokens().filter(|element| !matches!(
                element.kind(),
                SyntaxKind::Whitespace | SyntaxKind::Newline | SyntaxKind::LineComment | SyntaxKind::BlockComment,
            ));
            let _keyword = parts.next();
            let _subject = parts.next();
            let _colon = parts.next();
            let Some(role) = parts.next().and_then(|element| element.into_node()) else { continue; };
            if let Some(name) = role.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .find(|token| token.kind() == SyntaxKind::Identifier)
            {
                names.insert(name.text().into());
            }
        }
    }
    if found.len() != selected_roots.len() {
        return Err(HirAvailabilityError::StructuralProjection);
    }
    Ok(names)
}

#[cfg(any(feature = "shadow", test))]
fn selected_member_operation_paths(
    parsed: &ParsedFile,
    identity: &ModuleIdentity,
    indexes: &[source_exports::SourceExportIndex],
    selected_members: &std::collections::HashSet<yu_syntax::SourceNodeKey>,
    effects: &[source_annotation::SourceEffectDeclaration],
) -> Result<HashMap<Box<str>, source_exports::SourceOperationPathImport>, HirAvailabilityError> {
    use source_exports::{SourceExportResolveError, SourceOperationPathImport};
    if selected_members.iter().any(|key| !parsed.owns_source_key(key)) {
        return Err(HirAvailabilityError::ForeignSourceImport);
    }
    let keys = crate::source_identity::try_source_keys(parsed)?;
    let local_exports = index_source_exports(identity.clone(), parsed)?;
    let root = SyntaxNode::new_root(parsed.green().clone());
    let selected = root.descendants().filter(|node|
        keys.get(node).is_some_and(|key| selected_members.contains(key))
    ).collect::<Vec<_>>();
    let found = selected.iter().filter_map(|node| keys.get(node).cloned()).collect::<std::collections::HashSet<_>>();
    if found.len() != selected_members.len() { return Err(HirAvailabilityError::StructuralProjection); }

    let mut paths = HashMap::new();
    let mut imported_names = None;
    for member in selected {
        for expression in member.descendants().filter(|node| node.kind() == SyntaxKind::OperatorChain) {
            let mut children = expression.children();
            let Some(head) = children.next() else { continue; };
            if head.kind() != SyntaxKind::IdentifierExpression { continue; }
            let Some(head_token) = head.children_with_tokens().filter_map(|element| element.into_token())
                .find(|token| token.kind() == SyntaxKind::Identifier) else { continue; };
            let mut segments: Vec<Box<str>> = vec![head_token.text().into()];
            for tail in children.take_while(|tail| tail.kind() == SyntaxKind::PathTail) {
                if has_recovery(&tail) { return Err(HirAvailabilityError::SourceImportResolutionUnavailable); }
                let tokens = tail.children_with_tokens().filter(|element| !matches!(
                    element.kind(), SyntaxKind::Whitespace | SyntaxKind::Newline
                        | SyntaxKind::LineComment | SyntaxKind::BlockComment,
                )).collect::<Vec<_>>();
                let [separator, segment] = tokens.as_slice() else {
                    return Err(HirAvailabilityError::SourceImportResolutionUnavailable);
                };
                let separator = separator.as_token().ok_or(HirAvailabilityError::SourceImportResolutionUnavailable)?;
                let segment = segment.as_token().ok_or(HirAvailabilityError::SourceImportResolutionUnavailable)?;
                if separator.kind() != SyntaxKind::ColonColon || segment.kind() != SyntaxKind::Identifier {
                    return Err(HirAvailabilityError::SourceImportResolutionUnavailable);
                }
                segments.push(segment.text().into());
            }
            let path: Box<str> = segments.iter().map(AsRef::as_ref).collect::<Vec<_>>().join("::").into_boxed_str();
            if segments.len() == 2 {
                let mut local_families = Vec::new();
                for effect in effects.iter().filter(|effect|
                    effect.id.module.as_ref() == &identity.module
                        && effect.spelling.as_ref() == segments[0].as_ref()
                ) {
                    if !local_families.iter().any(|family: &&source_annotation::SourceEffectDeclaration|
                        family.id == effect.id
                    ) {
                        local_families.push(effect);
                    }
                }
                if !local_families.is_empty() {
                    let [family] = local_families.as_slice() else {
                        return Err(HirAvailabilityError::SourceImportResolutionUnavailable);
                    };
                    let mut operation_matches = Vec::new();
                    for operation in family.operations.iter().filter(|operation|
                        operation.spelling == segments[1]
                    ) {
                        if !operation_matches.iter().any(|previous: &&Arc<source_annotation::SourceOperationDeclaration>|
                            previous.id == operation.id
                        ) {
                            operation_matches.push(operation);
                        }
                    }
                    let [operation] = operation_matches.as_slice() else {
                        return Err(HirAvailabilityError::SourceImportResolutionUnavailable);
                    };
                    let declarations = local_exports.declarations.iter().filter(|declaration|
                        declaration.kind == SyntaxKind::ActDeclaration
                            && declaration.source == family.id.declaration
                            && declaration.name.as_deref() == Some(segments[0].as_ref())
                    ).collect::<Vec<_>>();
                    let [declaration] = declarations.as_slice() else {
                        return Err(HirAvailabilityError::SourceImportResolutionUnavailable);
                    };
                    let export = source_exports::SourceExportResolution {
                        module: source_exports::module_label(&identity.module)
                            .ok_or(HirAvailabilityError::SourceImportResolutionUnavailable)?,
                        name: segments[0].clone(),
                        declaration: (*declaration).clone(),
                        route: Vec::new(),
                    };
                    paths.insert(path, SourceOperationPathImport {
                        export,
                        operation: (*operation).clone(),
                    });
                    continue;
                }
                if imported_names.is_none() {
                    let selected_names = selected_source_names(parsed, selected_members)?;
                    let (_, names) = resolve_source_imports_selected(
                        parsed, identity, indexes, Some(&selected_names),
                    )?;
                    imported_names = Some(names);
                }
                let names = imported_names.as_ref().expect("initialized above");
                let family_export = match names.get(&segments[0]) {
                    Some(source_exports::SourceImportBinding::Resolved(export))
                        if export.declaration.kind == SyntaxKind::ActDeclaration => export,
                    Some(source_exports::SourceImportBinding::Ambiguous) => {
                        return Err(HirAvailabilityError::SourceImportResolutionUnavailable);
                    }
                    _ => continue,
                };
                let mut matches = Vec::new();
                for effect in effects.iter().filter(|effect|
                    effect.id.declaration == family_export.declaration.source
                        && source_exports::module_label(&effect.id.module).as_deref()
                            == Some(family_export.module.as_ref())
                        && effect.visibility == HirVisibility::Public
                ) {
                    for operation in effect.operations.iter().filter(|operation|
                        operation.spelling.as_ref() == segments[1].as_ref()
                            && operation.visibility == HirVisibility::Public
                    ) {
                        matches.push((family_export.clone(), operation.clone()));
                    }
                }
                matches.dedup_by(|left, right| left.1.id == right.1.id);
                match matches.as_slice() {
                    [(export, operation)] => {
                        paths.insert(path, SourceOperationPathImport { export: export.clone(), operation: operation.clone() });
                    }
                    [] => {}
                    _ => return Err(HirAvailabilityError::SourceImportResolutionUnavailable),
                }
                continue;
            }
            if segments.len() < 3 { continue; }
            let mut matches = Vec::new();
            for family_index in 1..segments.len() - 1 {
                let module = segments[..family_index].iter().map(AsRef::as_ref).collect::<Vec<_>>().join("::");
                let family_name = &segments[family_index];
                let export = match source_exports::resolve_public_export(indexes, &module, family_name) {
                    Ok(export) if export.declaration.kind == SyntaxKind::ActDeclaration => export,
                    Ok(_) | Err(SourceExportResolveError::MissingModule(_))
                        | Err(SourceExportResolveError::MissingExport { .. }) => continue,
                    Err(SourceExportResolveError::Ambiguous { .. }) => {
                        return Err(HirAvailabilityError::SourceImportResolutionUnavailable);
                    }
                    Err(_) => return Err(HirAvailabilityError::SourceImportResolutionUnavailable),
                };
                let Some(effect) = effects.iter().find(|effect|
                    effect.id.declaration == export.declaration.source
                        && effect.visibility == HirVisibility::Public
                ) else { continue; };
                for operation in effect.operations.iter().filter(|operation|
                    operation.spelling.as_ref() == segments.last().expect("nonempty path").as_ref()
                        && operation.visibility == HirVisibility::Public
                ) {
                    matches.push((export.clone(), operation.clone()));
                }
            }
            matches.dedup_by(|left, right| left.1.id == right.1.id);
            match matches.as_slice() {
                [(export, operation)] => {
                    paths.insert(path, SourceOperationPathImport { export: export.clone(), operation: operation.clone() });
                }
                [] => {}
                _ => return Err(HirAvailabilityError::SourceImportResolutionUnavailable),
            }
        }
    }
    Ok(paths)
}

fn selected_member_value_paths(
    parsed: &ParsedFile,
    indexes: &[source_exports::SourceExportIndex],
    selected_members: &std::collections::HashSet<yu_syntax::SourceNodeKey>,
) -> Result<HashMap<Box<str>, source_exports::SourceImportBinding>, HirAvailabilityError> {
    use source_exports::{SourceExportResolveError, SourceImportBinding};
    if selected_members.iter().any(|key| !parsed.owns_source_key(key)) {
        return Err(HirAvailabilityError::ForeignSourceImport);
    }
    let keys = crate::source_identity::try_source_keys(parsed)?;
    let root = SyntaxNode::new_root(parsed.green().clone());
    let selected = root.descendants().filter(|node|
        keys.get(node).is_some_and(|key| selected_members.contains(key))
    ).collect::<Vec<_>>();
    let found = selected.iter().filter_map(|node| keys.get(node).cloned()).collect::<std::collections::HashSet<_>>();
    if found.len() != selected_members.len() { return Err(HirAvailabilityError::StructuralProjection); }

    let mut paths = HashMap::new();
    for member in selected {
        for expression in member.descendants().filter(|node| node.kind() == SyntaxKind::OperatorChain) {
            let mut children = expression.children();
            let Some(head) = children.next() else { continue; };
            if head.kind() != SyntaxKind::IdentifierExpression { continue; }
            let Some(head_token) = head.children_with_tokens().filter_map(|element| element.into_token())
                .find(|token| token.kind() == SyntaxKind::Identifier) else { continue; };
            let mut segments: Vec<Box<str>> = vec![head_token.text().into()];
            for tail in children.take_while(|tail| tail.kind() == SyntaxKind::PathTail) {
                if has_recovery(&tail) { return Err(HirAvailabilityError::SourceImportResolutionUnavailable); }
                let tokens = tail.children_with_tokens().filter(|element| !matches!(
                    element.kind(), SyntaxKind::Whitespace | SyntaxKind::Newline
                        | SyntaxKind::LineComment | SyntaxKind::BlockComment,
                )).collect::<Vec<_>>();
                let [separator, segment] = tokens.as_slice() else {
                    return Err(HirAvailabilityError::SourceImportResolutionUnavailable);
                };
                let separator = separator.as_token().ok_or(HirAvailabilityError::SourceImportResolutionUnavailable)?;
                let segment = segment.as_token().ok_or(HirAvailabilityError::SourceImportResolutionUnavailable)?;
                if separator.kind() != SyntaxKind::ColonColon || segment.kind() != SyntaxKind::Identifier {
                    return Err(HirAvailabilityError::SourceImportResolutionUnavailable);
                }
                segments.push(segment.text().into());
            }
            if segments.len() < 2 { continue; }
            let path: Box<str> = segments.iter().map(AsRef::as_ref).collect::<Vec<_>>().join("::").into_boxed_str();
            let module = segments[..segments.len() - 1].iter().map(AsRef::as_ref).collect::<Vec<_>>().join("::");
            let name = segments.last().expect("nonempty qualified path");
            let export = match source_exports::resolve_public_export(indexes, &module, name) {
                Ok(export) if export.declaration.kind == SyntaxKind::BindingStatement && !export.declaration.recovered => export,
                Ok(export) if export.declaration.kind == SyntaxKind::BindingStatement => {
                    return Err(HirAvailabilityError::SourceImportResolutionUnavailable);
                }
                Ok(_) | Err(SourceExportResolveError::MissingModule(_))
                    | Err(SourceExportResolveError::MissingExport { .. }) => continue,
                Err(SourceExportResolveError::Ambiguous { .. }) => {
                    paths.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
                    paths.insert(path, SourceImportBinding::Ambiguous);
                    continue;
                }
                Err(_) => return Err(HirAvailabilityError::SourceImportResolutionUnavailable),
            };
            match paths.get(path.as_ref()) {
                Some(SourceImportBinding::Resolved(previous)) if previous.identity() == export.identity() => {}
                Some(_) => { paths.insert(path, SourceImportBinding::Ambiguous); }
                None => {
                    paths.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
                    paths.insert(path, SourceImportBinding::Resolved(export));
                }
            }
        }
    }
    Ok(paths)
}

fn source_import_environment(
    parsed: &ParsedFile,
    identity: &ModuleIdentity,
    parse_root: yu_syntax::SourceNodeKey,
    names: HashMap<Box<str>, source_exports::SourceImportBinding>,
    indexes: &[source_exports::SourceExportIndex],
) -> Result<source_exports::SourceImportEnvironment, HirAvailabilityError> {
    let mut environment = source_exports::SourceImportEnvironment::new(
        parse_root,
        identity.clone(),
        names,
    );
    environment.retain_syntax_operator_sources(parsed, indexes)?;
    Ok(environment)
}

impl SemanticImports {
    pub fn empty() -> Self {
        Self { caller_evidence: None, source_imports: None }
    }

    /// Retain source-authenticated names exported by the implicit prelude for
    /// identifier occurrences in this exact parsed file. Caller-supplied
    /// indexes are the source authority; this constructor proves their public
    /// route and binds the result to the consumer parse/module identity.
    pub fn with_implicit_prelude(
        parsed: &ParsedFile,
        identity: &ModuleIdentity,
        indexes: &[source_exports::SourceExportIndex],
    ) -> Result<Self, HirAvailabilityError> {
        let (parse_root, names) = resolve_implicit_prelude_imports(parsed, identity, indexes)?;
        Ok(Self { caller_evidence: None, source_imports: Some(source_import_environment(
            parsed, identity, parse_root, names, indexes,
        )?) })
    }

    /// Resolve all parse-owned `use` leaves against exact indexed source
    /// providers, then add implicit prelude names not shadowed by explicit
    /// imports. Glob candidates come only from the supplied provider indexes.
    pub fn with_source_imports(
        parsed: &ParsedFile,
        identity: &ModuleIdentity,
        indexes: &[source_exports::SourceExportIndex],
    ) -> Result<Self, HirAvailabilityError> {
        let (parse_root, names) = resolve_source_imports(parsed, identity, indexes)?;
        let mut source_imports = source_import_environment(parsed, identity, parse_root, names, indexes)?;
        source_imports.complete_source_uses = true;
        Ok(Self { caller_evidence: None, source_imports: Some(source_imports) })
    }

    /// As `with_source_imports`, while also retaining exact imported role and
    /// role-member source identities from the supplied provider index.
    #[cfg(any(feature = "shadow", test))]
    pub fn with_source_imports_and_role_indexes(
        parsed: &ParsedFile,
        identity: &ModuleIdentity,
        indexes: &[source_exports::SourceExportIndex],
        role_indexes: &[crate::shadow::SourceRoleImplIndex],
    ) -> Result<Self, HirAvailabilityError> {
        let (parse_root, names) = resolve_source_imports(parsed, identity, indexes)?;
        let mut source_imports = source_import_environment(parsed, identity, parse_root, names, indexes)?;
        retain_authenticated_role_imports(&mut source_imports, role_indexes)?;
        source_imports.complete_source_uses = true;
        Ok(Self { caller_evidence: None, source_imports: Some(source_imports) })
    }

    /// Resolves only names appearing in selected parse-owned direct roots.
    /// Pair this environment with `lower_module_with_selected_local_source`
    /// using the same root set so omitted module imports are not mistaken for
    /// unresolved names in roots that were deliberately projected away.
    #[cfg(any(feature = "shadow", test))]
    pub fn with_selected_source_imports(
        parsed: &ParsedFile,
        identity: &ModuleIdentity,
        indexes: &[source_exports::SourceExportIndex],
        selected_roots: &std::collections::HashSet<yu_syntax::SourceNodeKey>,
    ) -> Result<Self, HirAvailabilityError> {
        let selected_names = selected_source_names(parsed, selected_roots)?;
        let (parse_root, names) = resolve_source_imports_selected(parsed, identity, indexes, Some(&selected_names))?;
        Ok(Self { caller_evidence: None, source_imports: Some(source_import_environment(
            parsed, identity, parse_root, names, indexes,
        )?) })
    }

    /// Selected-root projection with exact imported role/member source IDs.
    #[cfg(any(feature = "shadow", test))]
    pub fn with_selected_source_imports_and_role_indexes(
        parsed: &ParsedFile,
        identity: &ModuleIdentity,
        indexes: &[source_exports::SourceExportIndex],
        selected_roots: &std::collections::HashSet<yu_syntax::SourceNodeKey>,
        role_indexes: &[crate::shadow::SourceRoleImplIndex],
    ) -> Result<Self, HirAvailabilityError> {
        let selected_names = selected_source_names(parsed, selected_roots)?;
        let (parse_root, names) = resolve_source_imports_selected(parsed, identity, indexes, Some(&selected_names))?;
        let mut source_imports = source_import_environment(parsed, identity, parse_root, names, indexes)?;
        retain_authenticated_role_imports(&mut source_imports, role_indexes)?;
        Ok(Self { caller_evidence: None, source_imports: Some(source_imports) })
    }

    /// Resolve qualified host-operation paths used by these exact member
    /// roots. Family exports and operation members retain separate source IDs.
    #[cfg(any(feature = "shadow", test))]
    pub fn with_selected_member_operations(
        parsed: &ParsedFile,
        identity: &ModuleIdentity,
        indexes: &[source_exports::SourceExportIndex],
        selected_members: &std::collections::HashSet<yu_syntax::SourceNodeKey>,
        role_indexes: &[crate::shadow::SourceRoleImplIndex],
        effects: &[source_annotation::SourceEffectDeclaration],
    ) -> Result<Self, HirAvailabilityError> {
        if identity.file != *identity.module.file() {
            return Err(HirAvailabilityError::InconsistentIdentity);
        }
        let operation_paths = selected_member_operation_paths(parsed, identity, indexes, selected_members, effects)?;
        let value_paths = selected_member_value_paths(parsed, indexes, selected_members)?;
        let mut imports = source_import_environment(
            parsed, identity, parsed.source_root().key(), value_paths, indexes,
        )?;
        imports.retain_operation_paths(operation_paths);
        retain_authenticated_role_imports(&mut imports, role_indexes)?;
        retain_implicit_prelude_role_ids(
            &mut imports, parsed, identity, indexes, role_indexes, selected_members,
        )?;
        Ok(Self { caller_evidence: None, source_imports: Some(imports) })
    }

    /// Retain exact identities for imported public role declarations when
    /// their provider role indexes are supplied and match the resolved export.
    #[cfg(any(feature = "shadow", test))]
    pub fn with_implicit_prelude_and_role_indexes(
        parsed: &ParsedFile,
        identity: &ModuleIdentity,
        indexes: &[source_exports::SourceExportIndex],
        role_indexes: &[crate::shadow::SourceRoleImplIndex],
    ) -> Result<Self, HirAvailabilityError> {
        let (parse_root, names) = resolve_implicit_prelude_imports(parsed, identity, indexes)?;
        let mut source_imports = source_import_environment(parsed, identity, parse_root, names, indexes)?;
        retain_authenticated_role_imports(&mut source_imports, role_indexes)?;
        Ok(Self { caller_evidence: None, source_imports: Some(source_imports) })
    }

    /// Retain opaque caller evidence for one exact parsed top-level declaration.
    /// Lowering verifies that the key is an admitted binding declaration in
    /// the resulting HIR. This does not validate the payload's meaning.
    pub fn with_caller_evidence<T>(
        parsed: &ParsedFile,
        identity: &ModuleIdentity,
        declaration: &yu_syntax::SourceNodeKey,
        payload: Arc<T>,
    ) -> Result<Self, HirAvailabilityError>
    where
        T: Any + Send + Sync,
    {
        if !parsed.owns_source_key(declaration) {
            return Err(HirAvailabilityError::ForeignCallerEvidenceSource);
        }
        let root = parsed.source_root().key();
        Ok(Self {
            caller_evidence: Some(CallerEvidenceBinding {
                parse_root: root,
                declaration: declaration.clone(),
                identity: identity.clone(),
                payload,
            }),
            source_imports: None,
        })
    }

    pub fn caller_evidence(&self) -> Option<&CallerEvidenceBinding> {
        self.caller_evidence.as_ref()
    }

    pub fn source_imports(&self) -> Option<&source_exports::SourceImportEnvironment> {
        self.source_imports.as_ref()
    }
}

#[cfg(any(feature = "shadow", test))]
fn retain_authenticated_role_imports(
    imports: &mut source_exports::SourceImportEnvironment,
    role_indexes: &[crate::shadow::SourceRoleImplIndex],
) -> Result<(), HirAvailabilityError> {
    use source_exports::SourceImportBinding;
    let mut role_ids = std::collections::HashMap::new();
    let mut role_member_ids = std::collections::HashMap::new();
    for (name, binding) in imports.names() {
        let SourceImportBinding::Resolved(resolution) = binding else { continue; };
        if resolution.declaration.kind != SyntaxKind::RoleDeclaration { continue; }
        let owner = crate::shadow::resolve_source_export_owner(&[], role_indexes, resolution)
            .map_err(|_| HirAvailabilityError::SourceImportResolutionUnavailable)?;
        let crate::shadow::SourceExportOwner::Role { declaration, .. } = owner else {
            return Err(HirAvailabilityError::SourceImportResolutionUnavailable);
        };
        let role_id = declaration.id.clone();
        role_ids.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        role_ids.insert(name.clone(), role_id.clone());
        let members = match crate::shadow::source_role_member_inventory(&role_id, role_indexes) {
            Ok(members) => members,
            Err(crate::shadow::SourceRoleMemberError::IdentityExhausted) => {
                return Err(HirAvailabilityError::IdentityExhausted);
            }
            Err(_) => continue,
        };
        role_member_ids.try_reserve(members.len()).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        for (member_name, member_id) in members {
            role_member_ids.insert((name.clone(), member_name), member_id);
        }
    }
    imports.retain_role_ids(role_ids);
    imports.retain_role_member_ids(role_member_ids);
    Ok(())
}

#[cfg(any(feature = "shadow", test))]
fn retain_implicit_prelude_role_ids(
    imports: &mut source_exports::SourceImportEnvironment,
    parsed: &ParsedFile,
    identity: &ModuleIdentity,
    indexes: &[source_exports::SourceExportIndex],
    role_indexes: &[crate::shadow::SourceRoleImplIndex],
    selected_members: &std::collections::HashSet<yu_syntax::SourceNodeKey>,
) -> Result<(), HirAvailabilityError> {
    use source_exports::SourceImportBinding;
    let selected_names = selected_source_names(parsed, selected_members)?;
    let (parse_root, names) = resolve_implicit_prelude_imports_selected(
        parsed, identity, indexes, Some(&selected_names),
    )?;
    let mut implicit = source_import_environment(parsed, identity, parse_root, names, indexes)?;
    retain_authenticated_role_imports(&mut implicit, role_indexes)?;

    let mut role_ids = std::collections::HashMap::new();
    for (name, binding) in imports.names() {
        if matches!(binding, SourceImportBinding::Resolved(resolution)
            if resolution.declaration.kind == SyntaxKind::RoleDeclaration) {
            if let Some(role) = imports.role_id(name) {
                role_ids.insert(name.clone(), role.clone());
            }
        }
    }
    for (name, binding) in implicit.names() {
        if imports.resolve(name).is_some()
            || !matches!(binding, SourceImportBinding::Resolved(resolution)
                if resolution.declaration.kind == SyntaxKind::RoleDeclaration) {
            continue;
        }
        if let Some(role) = implicit.role_id(name) {
            role_ids.insert(name.clone(), role.clone());
        }
    }
    imports.retain_role_ids(role_ids);
    Ok(())
}

impl std::fmt::Debug for SemanticImports {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.debug_struct("SemanticImports")
            .field("caller_evidence", &self.caller_evidence)
            .field("source_imports", &self.source_imports)
            .finish()
    }
}

impl PartialEq for SemanticImports {
    fn eq(&self, other: &Self) -> bool {
        self.caller_evidence == other.caller_evidence
            && self.source_imports == other.source_imports
    }
}

impl Eq for SemanticImports {}

/// Structural association of an opaque caller payload with one HIR input.
/// The payload's contents are not deeply immutable or semantically checked.
#[derive(Clone)]
pub struct CallerEvidenceBinding {
    parse_root: yu_syntax::SourceNodeKey,
    declaration: yu_syntax::SourceNodeKey,
    identity: ModuleIdentity,
    payload: Arc<dyn Any + Send + Sync>,
}

impl CallerEvidenceBinding {
    pub fn parse_root_key(&self) -> &yu_syntax::SourceNodeKey {
        &self.parse_root
    }

    pub fn declaration_key(&self) -> &yu_syntax::SourceNodeKey {
        &self.declaration
    }

    pub fn module_identity(&self) -> &ModuleIdentity {
        &self.identity
    }

    /// Reports only the retained Rust payload's concrete type.
    pub fn payload_is<T: Any>(&self) -> bool {
        self.payload.is::<T>()
    }
}

impl std::fmt::Debug for CallerEvidenceBinding {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.debug_struct("CallerEvidenceBinding")
            .field("parse_root", &self.parse_root)
            .field("declaration", &self.declaration)
            .field("identity", &self.identity)
            .field("payload", &"<opaque>")
            .finish()
    }
}

impl PartialEq for CallerEvidenceBinding {
    fn eq(&self, other: &Self) -> bool {
        self.parse_root == other.parse_root
            && self.declaration == other.declaration
            && self.identity == other.identity
            && Arc::ptr_eq(&self.payload, &other.payload)
    }
}

impl Eq for CallerEvidenceBinding {}

/// A stable definition identity within one source-root module.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct DefId {
    module: ModuleId,
    spelling: Box<str>,
    same_name_ordinal: u32,
}

impl DefId {
    pub fn module(&self) -> &ModuleId {
        &self.module
    }

    pub fn spelling(&self) -> &str {
        &self.spelling
    }

    pub fn same_name_ordinal(&self) -> u32 {
        self.same_name_ordinal
    }

    /// Returns the dynamic identity payload bytes that this `DefId`'s derived
    /// `Hash` and equality may scan.
    ///
    /// This includes the definition spelling plus the source-root module
    /// file-key realm and normalized workspace-relative path. It excludes
    /// fixed-size enum discriminants, string length metadata, pointer and
    /// container storage, and `same_name_ordinal`: those values participate in
    /// the derived operations but do not add a variable-length identity payload
    /// to scan.
    pub fn hash_eq_payload_bytes(&self) -> usize {
        let file_key = self.module.file().key();
        self.spelling.len()
            + file_key.realm().len()
            + file_key.normalized_workspace_relative_path().len()
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct HirErrorId(u32);

impl HirErrorId {
    pub fn index(self) -> u32 {
        self.0
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct HirDiagnosticId(u32);

impl HirDiagnosticId {
    pub fn index(self) -> u32 {
        self.0
    }
}

/// A lowering-order expression identity branded by its immutable HIR artifact.
///
/// The token is intentionally private and non-serializable. An ordinal is only
/// meaningful alongside this token, so independently lowered modules cannot
/// accidentally use each other's occurrence zero.
#[derive(Clone)]
pub struct HirOccurrenceId {
    artifact: Arc<HirArtifactToken>,
    ordinal: u32,
}

/// An admitted definition identity branded by the immutable HIR artifact that
/// owns it. The definition payload is shared with its binding so copying a
/// root never copies a `DefId` payload.
#[derive(Clone)]
pub struct DefinitionRootId {
    artifact: Arc<HirArtifactToken>,
    definition: Arc<DefId>,
}

impl DefinitionRootId {
    fn new(artifact: Arc<HirArtifactToken>, definition: Arc<DefId>) -> Self {
        Self {
            artifact,
            definition,
        }
    }
}

impl std::fmt::Debug for DefinitionRootId {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("DefinitionRootId")
            .finish_non_exhaustive()
    }
}

impl PartialEq for DefinitionRootId {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.artifact, &other.artifact) && self.definition == other.definition
    }
}

impl Eq for DefinitionRootId {}

impl Hash for DefinitionRootId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.artifact).hash(state);
        self.definition.hash(state);
    }
}

/// An actual direct-root expression, minted only while lowering that item.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct ExpressionRootId {
    occurrence: HirOccurrenceId,
}
impl ExpressionRootId {
    pub fn occurrence(&self) -> &HirOccurrenceId { &self.occurrence }
}

/// Source-backed member root for a role default or implementation body. It is
/// distinct from an admitted top-level definition and remains branded by the
/// HIR artifact that formed its source carrier.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum SourceMemberKind {
    Role,
    Implementation,
}

/// One exact identifier in a dotted method target Pattern.
#[derive(Clone, Debug)]
pub struct SourceMemberIdentifier {
    /// Source key of the IdentifierPattern or PatternFieldTail that owns it.
    pub source: yu_syntax::SourceNodeKey,
    /// Range of the identifier token itself.
    pub range: Range<usize>,
    pub spelling: Box<str>,
}

/// Structural source record for a Y2-compatible `receiver.method` Binding
/// target. Annotation data remains raw source; this record performs no type
/// parsing, receiver resolution or method selection.
#[derive(Clone, Debug)]
pub struct SourceMemberHeader {
    pub receiver: SourceMemberIdentifier,
    pub method: SourceMemberIdentifier,
    /// Ordinary identifier parameters following the dotted method target,
    /// such as `y` in `our x.add y = ...`.
    pub parameters: Vec<SourceMemberIdentifier>,
    pub annotation: Option<SourceMemberType>,
}

#[derive(Clone, Debug)]
pub struct SourceMemberType {
    pub source: yu_syntax::SourceNodeKey,
    pub range: Range<usize>,
    pub text: Box<str>,
}

#[derive(Clone)]
pub struct SourceMemberRootId {
    artifact: Arc<HirArtifactToken>,
    module: ModuleId,
    declaration: yu_syntax::SourceNodeKey,
    member: yu_syntax::SourceNodeKey,
    kind: SourceMemberKind,
}

impl SourceMemberRootId {
    fn new(
        artifact: Arc<HirArtifactToken>,
        module: ModuleId,
        declaration: yu_syntax::SourceNodeKey,
        member: yu_syntax::SourceNodeKey,
        kind: SourceMemberKind,
    ) -> Self {
        Self { artifact, module, declaration, member, kind }
    }
    pub fn module(&self) -> &ModuleId { &self.module }
    pub fn declaration_source_key(&self) -> &yu_syntax::SourceNodeKey { &self.declaration }
    pub fn member_source_key(&self) -> &yu_syntax::SourceNodeKey { &self.member }
    pub fn kind(&self) -> SourceMemberKind { self.kind }
}

impl std::fmt::Debug for SourceMemberRootId {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.debug_struct("SourceMemberRootId")
            .field("kind", &self.kind)
            .finish_non_exhaustive()
    }
}
impl PartialEq for SourceMemberRootId {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.artifact, &other.artifact)
            && self.module == other.module
            && self.declaration == other.declaration
            && self.member == other.member
            && self.kind == other.kind
    }
}
impl Eq for SourceMemberRootId {}
impl Hash for SourceMemberRootId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.artifact).hash(state);
        self.module.hash(state);
        self.declaration.hash(state);
        self.member.hash(state);
        self.kind.hash(state);
    }
}

/// Authentic source ownership without manufacturing a definition.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum SourceRootId {
    Definition(DefinitionRootId),
    Expression(ExpressionRootId),
    Member(SourceMemberRootId),
}
impl SourceRootId {
    pub fn definition_root(&self) -> Option<&DefinitionRootId> {
        match self { Self::Definition(root) => Some(root), Self::Expression(_) | Self::Member(_) => None }
    }
    pub fn expression_root(&self) -> Option<&ExpressionRootId> {
        match self { Self::Expression(root) => Some(root), Self::Definition(_) | Self::Member(_) => None }
    }
    pub fn member_root(&self) -> Option<&SourceMemberRootId> {
        match self { Self::Member(root) => Some(root), Self::Definition(_) | Self::Expression(_) => None }
    }
    fn artifact(&self) -> &Arc<HirArtifactToken> {
        match self {
            Self::Definition(root) => &root.artifact,
            Self::Expression(root) => &root.occurrence.artifact,
            Self::Member(root) => &root.artifact,
        }
    }
}
impl From<DefinitionRootId> for SourceRootId {
    fn from(root: DefinitionRootId) -> Self { Self::Definition(root) }
}
impl From<ExpressionRootId> for SourceRootId {
    fn from(root: ExpressionRootId) -> Self { Self::Expression(root) }
}

/// A local identity anchored to its enclosing artifact root.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct HirLocalId {
    owner: SourceRootId,
    ordinal: u32,
}
impl HirLocalId {
    pub fn source_root(&self) -> &SourceRootId { &self.owner }
    pub fn definition_root(&self) -> Option<&DefinitionRootId> { self.owner.definition_root() }
    pub fn ordinal(&self) -> u32 {
        self.ordinal
    }
}

/// An ordered parameter identity branded by the immutable HIR artifact that
/// owns its definition root.
///
/// ```compile_fail
/// use yu_hir::HirParameterId;
/// let _ = HirParameterId { owner: todo!(), ordinal: 0 };
/// ```
///
/// ```compile_fail
/// use yu_hir::HirParameterId;
/// fn requires_copy<T: Copy>() {}
/// requires_copy::<HirParameterId>();
/// ```
///
/// ```compile_fail
/// use yu_hir::HirParameterId;
/// fn requires_serialize<T: serde::Serialize>() {}
/// requires_serialize::<HirParameterId>();
/// ```
///
/// ```compile_fail
/// use yu_hir::HirParameterId;
/// let _ = HirParameterId::new(todo!(), 0);
/// ```
///
/// ```compile_fail
/// use yu_hir::HirParameterId;
/// let left: HirParameterId = todo!();
/// let right: HirParameterId = todo!();
/// let _ = left < right;
/// ```
#[derive(Clone)]
pub struct HirParameterId {
    owner: SourceRootId,
    ordinal: u32,
}

impl HirParameterId {
    fn new(owner: impl Into<SourceRootId>, ordinal: u32) -> Self {
        Self { owner: owner.into(), ordinal }
    }

    pub fn source_root(&self) -> &SourceRootId { &self.owner }
    pub fn definition_root(&self) -> Option<&DefinitionRootId> { self.owner.definition_root() }

    pub const fn ordinal(&self) -> u32 {
        self.ordinal
    }
}

impl std::fmt::Debug for HirParameterId {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("HirParameterId")
            .field("ordinal", &self.ordinal)
            .finish_non_exhaustive()
    }
}

impl PartialEq for HirParameterId {
    fn eq(&self, other: &Self) -> bool {
        self.owner == other.owner && self.ordinal == other.ordinal
    }
}

impl Eq for HirParameterId {}

impl Hash for HirParameterId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.owner.hash(state);
        self.ordinal.hash(state);
    }
}

impl HirOccurrenceId {
    fn new(artifact: Arc<HirArtifactToken>, ordinal: u32) -> Self {
        Self { artifact, ordinal }
    }

    pub const fn ordinal(&self) -> u32 {
        self.ordinal
    }
}

impl std::fmt::Debug for HirOccurrenceId {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("HirOccurrenceId")
            .field("ordinal", &self.ordinal)
            .finish_non_exhaustive()
    }
}

impl PartialEq for HirOccurrenceId {
    fn eq(&self, other: &Self) -> bool {
        self.ordinal == other.ordinal && Arc::ptr_eq(&self.artifact, &other.artifact)
    }
}

impl Eq for HirOccurrenceId {}

impl Hash for HirOccurrenceId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.artifact).hash(state);
        self.ordinal.hash(state);
    }
}

#[derive(Debug)]
struct HirArtifactToken {
    _serial: u64,
}

static NEXT_HIR_ARTIFACT: AtomicU64 = AtomicU64::new(0);

fn mint_artifact_token() -> Arc<HirArtifactToken> {
    Arc::new(HirArtifactToken {
        _serial: NEXT_HIR_ARTIFACT.fetch_add(1, Ordering::Relaxed),
    })
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HirName {
    spelling: String,
    range: Range<usize>,
}

impl HirName {
    pub fn spelling(&self) -> &str {
        &self.spelling
    }

    pub fn range(&self) -> &Range<usize> {
        &self.range
    }
}

#[derive(Clone, Debug)]
pub struct HirParameter {
    id: HirParameterId,
    name: HirName,
    range: Range<usize>,
    unit_pattern: bool,
}

impl HirParameter {
    pub fn id(&self) -> &HirParameterId {
        &self.id
    }

    pub fn name(&self) -> &HirName {
        &self.name
    }

    pub fn range(&self) -> &Range<usize> {
        &self.range
    }
}

impl PartialEq for HirParameter {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.range == other.range && self.unit_pattern == other.unit_pattern
    }
}

impl Eq for HirParameter {}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HirVisibility {
    Private,
    Our,
    Public,
}

#[derive(Clone, Debug)]
pub enum NameResolution {
    Resolved(DefId),
    Imported(source_exports::SourceExportId),
    Parameter(HirParameterId),
    Ambiguous,
    Unresolved,
}

impl PartialEq for NameResolution {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Resolved(left), Self::Resolved(right)) => left == right,
            (Self::Imported(left), Self::Imported(right)) => left == right,
            (Self::Parameter(left), Self::Parameter(right)) => left.ordinal == right.ordinal,
            (Self::Ambiguous, Self::Ambiguous) | (Self::Unresolved, Self::Unresolved) => true,
            _ => false,
        }
    }
}

impl Eq for NameResolution {}

/// Source-owned generalization eligibility frozen while lowering an admitted
/// binding. F5a recognizes only values; later computation forms remain
/// unclassified until their exact gate specifies them.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum EvaluationClass {
    FetchValue,
}

#[derive(Clone, Debug)]
pub enum ResolvedExpr {
    /// Structural source application with its associated operands. Ordinary HIR
    /// admission and the opt-in shadow route share this shape; neither occurrence
    /// asserts callability or supplies a Call typing rule. The opt-in route keeps
    /// its pending-structure error attached, while ordinary admission carries only
    /// authentic operand-resolution errors.
    Apply {
        occurrence: HirOccurrenceId,
        source_form: SyntaxKind,
        callee: Box<ResolvedExpr>,
        argument: Box<ResolvedExpr>,
        errors: Box<[HirErrorId]>,
        range: Range<usize>,
    },
    /// Retained parenthesized source structure; no semantic grouping rule is supplied.
    Group {
        occurrence: HirOccurrenceId,
        inner: Box<ResolvedExpr>,
        range: Range<usize>,
    },
    Lambda {
        occurrence: HirOccurrenceId,
        parameter: HirParameterId,
        body: Box<ResolvedExpr>,
        range: Range<usize>,
    },
    Integer {
        occurrence: HirOccurrenceId,
        spelling: String,
        range: Range<usize>,
    },
    Name {
        occurrence: HirOccurrenceId,
        name: HirName,
        resolution: NameResolution,
        range: Range<usize>,
    },
    Error {
        occurrence: HirOccurrenceId,
        errors: Box<[HirErrorId]>,
        range: Range<usize>,
    },
}

impl ResolvedExpr {
    pub fn occurrence(&self) -> &HirOccurrenceId {
        match self {
            Self::Apply { occurrence, .. } => occurrence,
            Self::Group { occurrence, .. }
            | Self::Lambda { occurrence, .. }
            | Self::Integer { occurrence, .. }
            | Self::Name { occurrence, .. }
            | Self::Error { occurrence, .. } => occurrence,
        }
    }

    pub fn range(&self) -> &Range<usize> {
        match self {
            Self::Apply { range, .. } => range,
            Self::Group { range, .. }
            | Self::Lambda { range, .. }
            | Self::Integer { range, .. }
            | Self::Name { range, .. }
            | Self::Error { range, .. } => range,
        }
    }
}

// Artifact identity protects cross-module lookup. It is not source semantics,
// so existing structural HIR equality intentionally continues to compare the
// lowered expression payload rather than the freshly minted artifact token.
impl PartialEq for ResolvedExpr {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Self::Apply {
                    source_form: left_form,
                    callee: left_callee,
                    argument: left_argument,
                    errors: left_errors,
                    range: left_range,
                    ..
                },
                Self::Apply {
                    source_form: right_form,
                    callee: right_callee,
                    argument: right_argument,
                    errors: right_errors,
                    range: right_range,
                    ..
                },
            ) => {
                left_form == right_form
                    && left_callee == right_callee
                    && left_argument == right_argument
                    && left_errors == right_errors
                    && left_range == right_range
            }
            (
                Self::Group {
                    inner: left,
                    range: left_range,
                    ..
                },
                Self::Group {
                    inner: right,
                    range: right_range,
                    ..
                },
            ) => left == right && left_range == right_range,
            (
                Self::Lambda {
                    parameter: left_parameter,
                    body: left_body,
                    range: left_range,
                    ..
                },
                Self::Lambda {
                    parameter: right_parameter,
                    body: right_body,
                    range: right_range,
                    ..
                },
            ) => {
                left_parameter.ordinal == right_parameter.ordinal
                    && left_body == right_body
                    && left_range == right_range
            }
            (
                Self::Integer {
                    spelling: left_spelling,
                    range: left_range,
                    ..
                },
                Self::Integer {
                    spelling: right_spelling,
                    range: right_range,
                    ..
                },
            ) => left_spelling == right_spelling && left_range == right_range,
            (
                Self::Name {
                    name: left_name,
                    resolution: left_resolution,
                    range: left_range,
                    ..
                },
                Self::Name {
                    name: right_name,
                    resolution: right_resolution,
                    range: right_range,
                    ..
                },
            ) => {
                left_name == right_name
                    && left_resolution == right_resolution
                    && left_range == right_range
            }
            (
                Self::Error {
                    errors: left_errors,
                    range: left_range,
                    ..
                },
                Self::Error {
                    errors: right_errors,
                    range: right_range,
                    ..
                },
            ) => left_errors == right_errors && left_range == right_range,
            _ => false,
        }
    }
}

impl Eq for ResolvedExpr {}

#[derive(Clone, Debug)]
pub struct HirBinding {
    id: Arc<DefId>,
    definition_root: DefinitionRootId,
    visibility: HirVisibility,
    name: HirName,
    parameters: Box<[HirParameter]>,
    #[allow(dead_code, reason = "frozen for the later exact generalization gate")]
    evaluation_class: Option<EvaluationClass>,
    value: ResolvedExpr,
    range: Range<usize>,
}

fn evaluation_class(value: &ResolvedExpr) -> Option<EvaluationClass> {
    match value {
        ResolvedExpr::Apply { .. } | ResolvedExpr::Group { .. } => None,
        ResolvedExpr::Lambda { body, .. }
            if matches!(body.as_ref(), ResolvedExpr::Apply { .. }) =>
        {
            None
        }
        ResolvedExpr::Lambda { .. }
        | ResolvedExpr::Integer { .. }
        | ResolvedExpr::Name {
            resolution: NameResolution::Resolved(_)
                | NameResolution::Imported(_)
                | NameResolution::Parameter(_),
            ..
        } => Some(EvaluationClass::FetchValue),
        ResolvedExpr::Name {
            resolution: NameResolution::Ambiguous | NameResolution::Unresolved,
            ..
        }
        | ResolvedExpr::Error { .. } => None,
    }
}

impl HirBinding {
    pub fn id(&self) -> &DefId {
        &self.id
    }
    pub fn definition_root(&self) -> &DefinitionRootId {
        &self.definition_root
    }
    pub fn visibility(&self) -> HirVisibility {
        self.visibility
    }
    pub fn name(&self) -> &HirName {
        &self.name
    }
    pub fn parameters(&self) -> &[HirParameter] {
        &self.parameters
    }
    pub fn value(&self) -> &ResolvedExpr {
        &self.value
    }
    pub fn range(&self) -> &Range<usize> {
        &self.range
    }
}

// Artifact identity protects root queries but is not source semantics, just
// like expression occurrence identity. Structural HIR equality excludes it.
impl PartialEq for HirBinding {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
            && self.visibility == other.visibility
            && self.name == other.name
            && self.parameters == other.parameters
            && self.value == other.value
            && self.range == other.range
    }
}

impl Eq for HirBinding {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HirItem {
    /// A static use statement admitted by the complete, parse-bound source
    /// import resolver. Actual names still carry their exact export identities.
    Import { range: Range<usize> },
    Binding(HirBinding),
    Expression(ResolvedExpr),
    Error {
        errors: Box<[HirErrorId]>,
        range: Range<usize>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HirErrorOrigin {
    Syntax,
    Lowering,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HirErrorAttachment {
    Module,
    DirectRootItem(u32),
    Definition(DefId),
    Value(DefId),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HirErrorKind {
    InheritedMissing,
    InheritedRawError,
    InheritedInvalid,
    UnsupportedItem,
    UnsupportedTarget,
    UnsupportedExpression,
    MissingBody,
    DuplicateDefinition,
    AmbiguousName,
    UnresolvedName,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HirError {
    id: HirErrorId,
    origin: HirErrorOrigin,
    attachment: HirErrorAttachment,
    range: Range<usize>,
    kind: HirErrorKind,
    diagnostic: Option<HirDiagnosticId>,
}

impl HirError {
    pub fn id(&self) -> HirErrorId {
        self.id
    }
    pub fn origin(&self) -> HirErrorOrigin {
        self.origin
    }
    pub fn attachment(&self) -> &HirErrorAttachment {
        &self.attachment
    }
    pub fn range(&self) -> &Range<usize> {
        &self.range
    }
    pub fn kind(&self) -> HirErrorKind {
        self.kind
    }
    pub fn diagnostic(&self) -> Option<HirDiagnosticId> {
        self.diagnostic
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HirDiagnostic {
    id: HirDiagnosticId,
    error: HirErrorId,
    kind: HirErrorKind,
    range: Range<usize>,
}

impl HirDiagnostic {
    pub fn id(&self) -> HirDiagnosticId {
        self.id
    }
    pub fn error(&self) -> HirErrorId {
        self.error
    }
    pub fn kind(&self) -> HirErrorKind {
        self.kind
    }
    pub fn range(&self) -> &Range<usize> {
        &self.range
    }
}

#[derive(Clone, Debug)]
pub struct HirModule {
    artifact: Arc<HirArtifactToken>,
    caller_evidence: Option<CallerEvidenceBinding>,
    source_imports: Option<source_exports::SourceImportEnvironment>,
    pub(crate) source_identity: Option<crate::source_identity::HirSourceIdentity>,
    #[cfg(any(feature = "shadow", test))]
    pub(crate) captured_source: Option<(DefinitionRootId, Arc<crate::shadow::ShadowArtifact>)>,
    pub(crate) source_parsed: Option<ParsedFile>,
    pub(crate) local_sources: HashMap<DefinitionRootId, local_source::LocalSource>,
    #[cfg(any(feature = "shadow", test))]
    pub(crate) effect_declarations: Vec<source_annotation::SourceEffectDeclaration>,
    #[cfg(any(feature = "shadow", test))]
    pub(crate) role_declarations: Vec<source_role::SourceRoleDeclaration>,
    #[cfg(any(feature = "shadow", test))]
    pub(crate) implementation_declarations: Vec<source_impl::SourceImplementationDeclaration>,
    expression_roots: HashMap<HirOccurrenceId, ExpressionRootId>,
    source_carriers: Vec<(SourceRootId, local_source::SourceCarrierOutcome)>,
    source_carrier_indices: HashMap<SourceRootId, usize>,
    source_member_carriers: Vec<(SourceRootId, local_source::SourceCarrierOutcome)>,
    source_member_carrier_indices: HashMap<SourceRootId, usize>,
    identity: ModuleIdentity,
    source_revision: SourceRevision,
    items: Vec<HirItem>,
    errors: Vec<HirError>,
    diagnostics: Vec<HirDiagnostic>,
    definition_root_allocation_bytes: usize,
    definition_root_def_id_clone_bytes: usize,
}

impl HirModule {
    /// Ordinary binding/expression outcomes in direct-root source order.
    /// The opt-in binding adapter keeps its existing single-owned binding map.
    pub fn source_carrier_outcomes(&self) -> &[(SourceRootId, local_source::SourceCarrierOutcome)] {
        &self.source_carriers
    }
    /// Source-backed bodies of role and implementation members, kept apart
    /// from module direct roots because they are not independently executable.
    pub fn source_member_carrier_outcomes(&self) -> &[(SourceRootId, local_source::SourceCarrierOutcome)] {
        &self.source_member_carriers
    }
    /// Resolves only the original occurrence of an actual expression item.
    pub fn expression_root(&self, occurrence: &HirOccurrenceId)
        -> Result<Option<&ExpressionRootId>, HirAvailabilityError>
    {
        if !self.owns_occurrence(occurrence) { return Err(HirAvailabilityError::InconsistentIdentity); }
        Ok(self.expression_roots.get(occurrence))
    }
    pub fn owns_expression_root(&self, root: &ExpressionRootId) -> bool {
        self.expression_roots.get(root.occurrence()) == Some(root)
    }
    pub fn owns_source_root(&self, root: &SourceRootId) -> bool {
        match root {
            SourceRootId::Definition(root) => self.owns_definition_root(root),
            SourceRootId::Expression(root) => self.owns_expression_root(root),
            SourceRootId::Member(root) => Arc::ptr_eq(&self.artifact, &root.artifact)
                && root.module == *self.identity.module()
                && self.source_parsed.as_ref().is_some_and(|parsed|
                    parsed.owns_source_key(&root.declaration)
                        && parsed.owns_source_key(&root.member)),
        }
    }
    #[cfg(any(feature = "shadow", test))]
    pub(crate) fn source_member_root(
        &self,
        module: ModuleId,
        declaration: yu_syntax::SourceNodeKey,
        member: yu_syntax::SourceNodeKey,
        kind: SourceMemberKind,
    ) -> SourceRootId {
        SourceRootId::Member(SourceMemberRootId::new(
            self.artifact.clone(), module, declaration, member, kind,
        ))
    }
    pub fn source_carrier_for(&self, root: &SourceRootId)
        -> Result<Option<&local_source::SourceCarrierOutcome>, HirAvailabilityError>
    {
        if !self.owns_source_root(root) { return Err(HirAvailabilityError::InconsistentIdentity); }
        Ok(self.source_carrier_indices.get(root).map(|index| &self.source_carriers[*index].1)
            .or_else(|| self.source_member_carrier_indices.get(root).map(|index| &self.source_member_carriers[*index].1)))
    }
    /// Joins an authenticated imported operator body receipt to its existing
    /// direct-expression source root in this exact provider HIR artifact.
    #[cfg(any(feature = "shadow", test))]
    pub fn source_operator_root_for(
        &self,
        owner: &source_exports::SourceOperatorOwner,
        provider_index: &source_exports::SourceExportIndex,
    ) -> Result<Option<SourceRootId>, HirAvailabilityError> {
        if self.identity.module() != owner.module()
            || provider_index.module != *owner.module()
            || provider_index.revision != owner.revision()
        {
            return Ok(None);
        }
        let Some(indexed_owner) = provider_index.operator_owner_for_receipt(
            owner.module(), owner.revision(), owner.declaration_range(), owner.spelling(), owner.fixity(),
        ) else { return Ok(None); };
        if &indexed_owner != owner { return Ok(None); }
        let Some(parsed) = &self.source_parsed else { return Ok(None); };
        if !parsed.owns_source_key(owner.declaration()) || !parsed.owns_source_key(owner.body()) {
            return Ok(None);
        }
        let mut found = None;
        for (root, outcome) in &self.source_carriers {
            let SourceRootId::Expression(expression_root) = root else { continue; };
            if self.expression_source_key(expression_root)? != Some(owner.body()) { continue; }
            let local_source::SourceCarrierOutcome::Supported(source) = outcome else { continue; };
            if source.source_root() != root
                || source.expression(source.body()).is_none_or(|body| body.range != *owner.body_range())
                || found.replace(root.clone()).is_some()
            {
                return Ok(None);
            }
        }
        Ok(found)
    }
    pub fn source_carrier(&self, root: &DefinitionRootId)
        -> Result<Option<&local_source::SourceCarrierOutcome>, HirAvailabilityError>
    {
        self.source_carrier_for(&SourceRootId::Definition(root.clone()))
    }
    pub fn local_source_for(&self, root: &SourceRootId)
        -> Result<Option<&local_source::LocalSource>, HirAvailabilityError>
    {
        Ok(match self.source_carrier_for(root)? {
            Some(local_source::SourceCarrierOutcome::Supported(source)) => Some(source),
            Some(local_source::SourceCarrierOutcome::Unsupported(_)) => None,
            None => root.definition_root().and_then(|root| self.local_sources.get(root)),
        })
    }
    /// Definition-only compatibility adapter over the authentic source owner.
    pub fn local_source(&self, root: &DefinitionRootId)
        -> Result<Option<&local_source::LocalSource>, HirAvailabilityError>
    {
        self.local_source_for(&SourceRootId::Definition(root.clone()))
    }
    /// Exact parse-owned origin retained for a definition from this artifact.
    pub fn definition_source_key(&self, root: &DefinitionRootId)
        -> Result<Option<&yu_syntax::SourceNodeKey>, HirAvailabilityError>
    {
        if !self.owns_definition_root(root) { return Err(HirAvailabilityError::InconsistentIdentity); }
        Ok(self.source_identity.as_ref().and_then(|identity| identity.definitions.get(root)))
    }
    pub fn expression_source_key(&self, root: &ExpressionRootId)
        -> Result<Option<&yu_syntax::SourceNodeKey>, HirAvailabilityError>
    {
        if !self.owns_expression_root(root) { return Err(HirAvailabilityError::InconsistentIdentity); }
        Ok(self.source_identity.as_ref().and_then(|identity| identity.expressions.get(root)))
    }
    pub fn source_root_source_key<'a>(&'a self, root: &'a SourceRootId)
        -> Result<Option<&'a yu_syntax::SourceNodeKey>, HirAvailabilityError>
    {
        match root {
            SourceRootId::Definition(root) => self.definition_source_key(root),
            SourceRootId::Expression(root) => self.expression_source_key(root),
            SourceRootId::Member(member) => {
                if !self.owns_source_root(root) { return Err(HirAvailabilityError::InconsistentIdentity); }
                Ok(Some(&member.member))
            }
        }
    }
    /// Exact source node for an ordinary or retained structural occurrence.
    pub fn occurrence_source_key(&self, occurrence: &HirOccurrenceId)
        -> Result<Option<&yu_syntax::SourceNodeKey>, HirAvailabilityError>
    {
        if !self.owns_occurrence(occurrence) { return Err(HirAvailabilityError::InconsistentIdentity); }
        Ok(self.source_identity.as_ref().and_then(|identity| identity.occurrences.get(occurrence)))
    }
    /// Checks that a retained tuple-pattern source key is an element of the
    /// exact local case occurrence and root that candidate inference owns.
    pub fn owns_tuple_case_pattern_source(
        &self,
        root: &SourceRootId,
        occurrence: &HirOccurrenceId,
        pattern: &yu_syntax::SourceNodeKey,
        local_slot: u32,
    ) -> Result<bool, HirAvailabilityError> {
        let Some(source) = self.local_source_for(root)? else { return Ok(false); };
        if source.source_root() != root { return Err(HirAvailabilityError::InconsistentIdentity); }
        let Some(expression) = source.expressions().iter().find(|expression| &expression.occurrence == occurrence) else {
            return Ok(false);
        };
        let Some(parsed) = self.source_parsed.as_ref() else { return Ok(false); };
        if !parsed.owns_source_key(pattern) { return Ok(false); }
        let local_slot = usize::try_from(local_slot).map_err(|_| HirAvailabilityError::InconsistentIdentity)?;
        Ok(matches!(
            &expression.form,
            local_source::LocalSourceForm::Case { arms, .. }
                if arms.get(local_slot).is_some_and(|arm| matches!(
                    &arm.pattern,
                    local_source::LocalSourceCasePattern::Tuple { source, .. } if source == pattern
                ))
        ))
    }
    /// Retains named and inline parameter origins without reconstructing binders.
    pub fn parameter_source_origin(&self, parameter: &HirParameterId)
        -> Result<Option<&crate::HirParameterSourceOrigin>, HirAvailabilityError>
    {
        if !self.owns_source_root(parameter.source_root()) { return Err(HirAvailabilityError::InconsistentIdentity); }
        Ok(self.source_identity.as_ref().and_then(|identity| identity.parameters.get(parameter)))
    }
    /// Tests whether a branded occurrence was minted by this exact artifact.
    pub fn owns_occurrence(&self, occurrence: &HirOccurrenceId) -> bool {
        Arc::ptr_eq(&self.artifact, &occurrence.artifact)
    }

    /// Tests whether a branded definition root was minted by this exact artifact.
    pub fn owns_definition_root(&self, root: &DefinitionRootId) -> bool {
        Arc::ptr_eq(&self.artifact, &root.artifact)
    }

    pub fn owns_parameter(&self, parameter: &HirParameterId) -> bool {
        Arc::ptr_eq(&self.artifact, parameter.owner.artifact())
            && self.items.iter().any(|item| {
                matches!(item, HirItem::Binding(binding)
                    if Some(&binding.definition_root) == parameter.definition_root()
                        && binding.parameters.iter().any(|candidate| candidate.id == *parameter))
            })
    }

    pub fn identity(&self) -> &ModuleIdentity {
        &self.identity
    }
    /// Returns caller evidence associated structurally with this exact HIR.
    /// Presence is not semantic validation.
    pub fn caller_evidence(&self) -> Option<&CallerEvidenceBinding> {
        self.caller_evidence.as_ref()
    }
    pub fn source_imports(&self) -> Option<&source_exports::SourceImportEnvironment> {
        self.source_imports.as_ref()
    }
    pub fn source_revision(&self) -> SourceRevision {
        self.source_revision
    }
    pub fn items(&self) -> &[HirItem] {
        &self.items
    }
    pub fn errors(&self) -> &[HirError] {
        &self.errors
    }
    pub fn diagnostics(&self) -> &[HirDiagnostic] {
        &self.diagnostics
    }
    /// Storage reserved for definition roots in this immutable HIR artifact.
    pub const fn definition_root_allocation_bytes(&self) -> usize {
        self.definition_root_allocation_bytes
    }
    /// Definition roots share their binding's `DefId` reference rather than
    /// cloning a definition payload.
    pub const fn definition_root_def_id_clone_bytes(&self) -> usize {
        self.definition_root_def_id_clone_bytes
    }
}

impl PartialEq for HirModule {
    fn eq(&self, other: &Self) -> bool {
        self.identity == other.identity
            && self.source_revision == other.source_revision
            && self.items == other.items
            && self.source_imports == other.source_imports
            && self.errors == other.errors
            && self.diagnostics == other.diagnostics
    }
}

impl Eq for HirModule {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HirAvailabilityError {
    InconsistentIdentity,
    StructuralProjection,
    ExactOperatorEnvironment,
    IdentityExhausted,
    ForeignCallerEvidenceSource,
    ForeignCallerEvidenceModule,
    CallerEvidenceNotDeclaration,
    ForeignSourceImport,
    SourceImportResolutionUnavailable,
}

/// Lowers direct-root bindings and expressions against one complete local namespace.
pub fn lower_module(
    identity: ModuleIdentity,
    parsed: &ParsedFile,
    imports: SemanticImports,
) -> Result<HirModule, HirAvailabilityError> {
    let mut counters = LoweringCounters::default();
    counters.source_identity = Some(crate::source_identity::HirSourceIdentity::new(parsed));
    counters.source_nodes = crate::source_identity::try_source_keys(parsed)?;
    counters.ordinary_source_carriers = true;
    lower_module_with_counters(identity, parsed, imports, &mut counters)
}

#[cfg(any(feature = "shadow", test))]
pub(crate) fn lower_module_with_source_identity(
    identity: ModuleIdentity,
    parsed: &ParsedFile,
    imports: SemanticImports,
) -> Result<HirModule, HirAvailabilityError> {
    let mut counters = LoweringCounters::default();
    counters.source_identity = Some(crate::source_identity::HirSourceIdentity::new(parsed));
    counters.source_nodes = crate::source_identity::source_keys(parsed);
    lower_module_with_counters(identity, parsed, imports, &mut counters)
}

#[cfg(any(feature = "shadow", test))]
pub(crate) fn lower_module_with_shadow_applications(
    identity: ModuleIdentity,
    parsed: &ParsedFile,
    imports: SemanticImports,
) -> Result<HirModule, HirAvailabilityError> {
    let mut counters = LoweringCounters::default();
    counters.source_identity = Some(crate::source_identity::HirSourceIdentity::new(parsed));
    counters.source_nodes = crate::source_identity::source_keys(parsed);
    counters.shadow_applications = true;
    lower_module_with_counters(identity, parsed, imports, &mut counters)
}

#[cfg(any(feature = "shadow", test))]
pub(crate) fn lower_module_with_local_source(
    identity: ModuleIdentity,
    parsed: &ParsedFile,
    imports: SemanticImports,
) -> Result<HirModule, HirAvailabilityError> {
    let mut counters = LoweringCounters::default();
    counters.source_identity = Some(crate::source_identity::HirSourceIdentity::new(parsed));
    counters.source_nodes = crate::source_identity::source_keys(parsed);
    counters.local_source = true;
    lower_module_with_counters(identity, parsed, imports, &mut counters)
}

#[cfg(any(feature = "shadow", test))]
pub(crate) fn lower_module_with_member_sources(
    identity: ModuleIdentity,
    parsed: &ParsedFile,
    imports: SemanticImports,
) -> Result<HirModule, HirAvailabilityError> {
    let mut counters = LoweringCounters::default();
    counters.source_identity = Some(crate::source_identity::HirSourceIdentity::new(parsed));
    counters.source_nodes = crate::source_identity::source_keys(parsed);
    counters.member_sources = true;
    lower_module_with_counters(identity, parsed, imports, &mut counters)
}

#[cfg(any(feature = "shadow", test))]
pub(crate) fn lower_module_with_selected_member_sources(
    identity: ModuleIdentity,
    parsed: &ParsedFile,
    imports: SemanticImports,
    selected_members: std::collections::HashSet<yu_syntax::SourceNodeKey>,
) -> Result<HirModule, HirAvailabilityError> {
    if selected_members.iter().any(|member| !parsed.owns_source_key(member)) {
        return Err(HirAvailabilityError::ForeignSourceImport);
    }
    let mut counters = LoweringCounters::default();
    counters.source_identity = Some(crate::source_identity::HirSourceIdentity::new(parsed));
    counters.source_nodes = crate::source_identity::source_keys(parsed);
    counters.member_sources = true;
    counters.selected_member_sources = Some(selected_members);
    // A member-only provider contributes its exact member carrier, not the
    // unrelated direct module roots from the file that happened to contain it.
    counters.selected_local_source_roots = Some(std::collections::HashSet::new());
    lower_module_with_counters(identity, parsed, imports, &mut counters)
}

#[cfg(any(feature = "shadow", test))]
pub(crate) fn lower_module_with_selected_local_source(
    identity: ModuleIdentity,
    parsed: &ParsedFile,
    imports: SemanticImports,
    selected_roots: std::collections::HashSet<yu_syntax::SourceNodeKey>,
) -> Result<HirModule, HirAvailabilityError> {
    if selected_roots.iter().any(|root| !parsed.owns_source_key(root)) {
        return Err(HirAvailabilityError::ForeignSourceImport);
    }
    let mut counters = LoweringCounters::default();
    counters.source_identity = Some(crate::source_identity::HirSourceIdentity::new(parsed));
    counters.source_nodes = crate::source_identity::source_keys(parsed);
    counters.local_source = true;
    counters.selected_local_source_roots = Some(selected_roots);
    lower_module_with_counters(identity, parsed, imports, &mut counters)
}

#[cfg(any(feature = "shadow", test))]
pub(crate) fn index_role_impl_sources(
    identity: ModuleIdentity,
    parsed: &ParsedFile,
) -> Result<(
    Vec<source_role::SourceRoleDeclaration>,
    Vec<source_impl::SourceImplementationDeclaration>,
), HirAvailabilityError> {
    if identity.file != *identity.module.file() {
        return Err(HirAvailabilityError::InconsistentIdentity);
    }
    let mut counters = LoweringCounters::default();
    counters.source_nodes = crate::source_identity::try_source_keys(parsed)?;
    let root = SyntaxNode::new_root(parsed.green().clone());
    let roles = source_role::declarations(&root, identity.module(), &counters)?;
    let implementations = source_impl::declarations(&root, identity.module(), &counters)?;
    Ok((roles, implementations))
}

#[cfg(any(feature = "shadow", test))]
pub(crate) fn index_source_effects(
    identity: ModuleIdentity,
    parsed: &ParsedFile,
    selected: &std::collections::HashSet<yu_syntax::SourceNodeKey>,
) -> Result<Vec<source_annotation::SourceEffectDeclaration>, HirAvailabilityError> {
    if identity.file != *identity.module.file() {
        return Err(HirAvailabilityError::InconsistentIdentity);
    }
    let mut counters = LoweringCounters::default();
    counters.source_nodes = crate::source_identity::try_source_keys(parsed)?;
    let root = SyntaxNode::new_root(parsed.green().clone());
    source_annotation::declarations_selected(&root, identity.module(), &mut counters, Some(selected))
        .map_err(Into::into)
}

pub fn index_source_exports(
    identity: ModuleIdentity,
    parsed: &ParsedFile,
) -> Result<source_exports::SourceExportIndex, HirAvailabilityError> {
    if identity.file != *identity.module.file() {
        return Err(HirAvailabilityError::InconsistentIdentity);
    }
    let mut counters = LoweringCounters::default();
    counters.source_nodes = crate::source_identity::try_source_keys(parsed)?;
    let root = SyntaxNode::new_root(parsed.green().clone());
    source_exports::index(
        &root,
        identity.module(),
        parsed.revision(),
        parsed.header().operators(),
        &counters,
    )
}

fn lower_module_with_counters(
    identity: ModuleIdentity,
    parsed: &ParsedFile,
    imports: SemanticImports,
    counters: &mut LoweringCounters,
) -> Result<HirModule, HirAvailabilityError> {
    if identity.file != *identity.module.file() {
        return Err(HirAvailabilityError::InconsistentIdentity);
    }
    if let Some(binding) = imports.caller_evidence.as_ref() {
        if binding.identity != identity {
            return Err(HirAvailabilityError::ForeignCallerEvidenceModule);
        }
        if !parsed.owns_source_key(&binding.parse_root)
            || binding.parse_root != parsed.source_root().key()
            || !parsed.owns_source_key(&binding.declaration)
        {
            return Err(HirAvailabilityError::ForeignCallerEvidenceSource);
        }
    }
    if let Some(source_imports) = imports.source_imports.as_ref() {
        if source_imports.identity() != &identity {
            return Err(HirAvailabilityError::ForeignSourceImport);
        }
        if source_imports.parse_root() != &parsed.source_root().key()
            || !parsed.owns_source_key(source_imports.parse_root())
        {
            return Err(HirAvailabilityError::ForeignSourceImport);
        }
    }
    let recoveries = validated_recoveries(parsed)?;
    let root = SyntaxNode::new_root(parsed.green().clone());
    if counters.ordinary_source_carriers || counters.local_source || counters.member_sources {
        let associations = crate::associate_operator_chains(parsed);
        let mut uses = HashMap::new();
        let mut chains = HashMap::new();
        for chain in associations.chains() {
            retain_associated_operator_uses(chain.expression(), &mut uses)?;
            let tree = Arc::new(chain.expression().clone());
            retain_associated_operator_chains(&tree, &tree, &mut chains)?;
        }
        counters.source_operator_uses = uses;
        counters.source_associated_chains = chains;
    }
    #[cfg(any(feature = "shadow", test))]
    if counters.local_source {
        counters.effect_declarations = if counters.selected_local_source_roots.is_some() {
            // A selected provider root carries exact imported operations in
            // SourceImportEnvironment::operation_paths. Scanning every Act in
            // the provider file would make an unrelated host declaration a
            // prerequisite for retaining that binding's LocalSource.
            let no_local_effects = std::collections::HashSet::new();
            source_annotation::declarations_selected(
                &root, identity.module(), counters, Some(&no_local_effects),
            )?
        } else {
            source_annotation::declarations(&root, identity.module(), counters)?
        };
    }
    #[cfg(any(feature = "shadow", test))]
    if counters.local_source || counters.member_sources {
        counters.role_declarations =
            source_role::declarations(&root, identity.module(), counters)?;
        counters.implementation_declarations =
            source_impl::declarations(&root, identity.module(), counters)?;
    }
    let mut plans = Vec::new();
    for (index, node) in root.children().enumerate() {
        let ordinal = u32::try_from(index).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        let mut plan = plan_root(node, ordinal, &identity, counters)?;
        if plan.node.kind() == SyntaxKind::UseDeclaration
            && !has_recovery(&plan.node)
            && imports.source_imports.as_ref().is_some_and(|environment| environment.complete_source_uses)
        {
            plan.kind = RootPlanKind::Import;
        }
        plans.push(plan);
    }
    let selected_ordinals = if let Some(selected) = counters.selected_local_source_roots.as_ref() {
        let mut ordinals = std::collections::HashSet::new();
        ordinals.try_reserve(selected.len()).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        for plan in &plans {
            if counters.source_nodes.get(&plan.node).is_some_and(|source| selected.contains(source)) {
                ordinals.insert(plan.ordinal);
            }
        }
        if ordinals.len() != selected.len() {
            return Err(HirAvailabilityError::StructuralProjection);
        }
        Some(ordinals)
    } else { None };
    let partition = partition_recoveries(&recoveries, plans.len(), counters)?;
    let namespace = namespace(&mut plans, imports.source_imports.as_ref())?;
    let mut sink = ErrorSink::default();
    let root_errors = emit_structural_errors(&recoveries, &partition, &plans, &mut sink, counters)?;

    #[cfg(any(feature = "shadow", test))]
    if counters.local_source {
        for (declaration, plan) in counters.effect_declarations.iter().zip(
            plans
                .iter()
                .filter(|plan| plan.node.kind() == SyntaxKind::ActDeclaration),
        ) {
            let ordinal = plan.ordinal;
            if counters
                .effect_namespace
                .get(declaration.spelling.as_ref())
                .is_some_and(|ids| ids.len() > 1)
            {
                sink.lowering(
                    HirErrorKind::DuplicateDefinition,
                    HirErrorAttachment::DirectRootItem(ordinal),
                    declaration.range.clone(),
                )?;
            }
            for member in &declaration.operations {
                if counters
                    .operation_namespace
                    .get(&(declaration.id.clone(), member.spelling.clone()))
                    .is_some_and(|members| members.len() > 1)
                {
                    sink.lowering(
                        HirErrorKind::DuplicateDefinition,
                        HirErrorAttachment::DirectRootItem(ordinal),
                        member.range.clone(),
                    )?;
                }
            }
        }
    }

    let artifact = mint_artifact_token();
    let mut items = Vec::with_capacity(plans.len());
    let mut expression_roots = HashMap::new();
    let mut next_occurrence_ordinal = 0u32;
    let mut scope = ScopeStack::default();
    #[cfg(any(feature = "shadow", test))]
    let mut effect_ordinal = 0usize;
    for (plan, errors) in plans.iter().zip(root_errors) {
        let occurrence = next_occurrence(&artifact, &mut next_occurrence_ordinal)?;
        if matches!(plan.kind, RootPlanKind::DirectExpression) {
            expression_roots.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
            let root = ExpressionRootId { occurrence: occurrence.clone() };
            if let Some(source) = &mut counters.source_identity {
                let key = counters.source_nodes.get(&plan.node)
                    .ok_or(HirAvailabilityError::StructuralProjection)?;
                source.expressions.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
                source.expressions.insert(root.clone(), key.clone());
            }
            expression_roots.insert(occurrence.clone(), root);
        }
        let definition_root = match &plan.kind {
            RootPlanKind::Binding(admitted) => {
                Some(DefinitionRootId::new(artifact.clone(), admitted.id.clone()))
            }
            RootPlanKind::Import | RootPlanKind::DirectExpression | RootPlanKind::Unsupported(_) => None,
        };
        if let (Some(source), Some(definition)) = (&mut counters.source_identity, &definition_root)
        {
            if let Some(key) = counters.source_nodes.get(&plan.node) {
                source.record_definition(definition.clone(), key.clone());
            }
        }
        if definition_root.is_some() {
            counters.definition_root_allocation_bytes += std::mem::size_of::<DefinitionRootId>();
        }
        let item = lower_plan(
            plan,
            parsed,
            &namespace,
            errors.item,
            errors.value,
            &mut sink,
            counters,
            occurrence,
            definition_root,
            &artifact,
            &mut next_occurrence_ordinal,
            &mut scope,
        )?;
        #[cfg(any(feature = "shadow", test))]
        if counters.local_source
            && counters.selected_local_source_roots.is_none()
            && plan.node.kind() == SyntaxKind::ActDeclaration
        {
            let declaration = counters
                .effect_declarations
                .get_mut(effect_ordinal)
                .ok_or(HirAvailabilityError::StructuralProjection)?;
            effect_ordinal += 1;
            if let HirItem::Error { errors, .. } = &item {
                declaration
                    .placeholder_errors
                    .extend(errors.iter().copied().filter(|id| {
                        sink.errors.iter().any(|error| {
                            error.id == *id && error.kind == HirErrorKind::UnsupportedItem
                        })
                    }));
            }
        }
        items.push(item);
    }
    // Binding carrier allocation stays a complete first pass, preserving all
    // previously published binding-carrier ordinals in mixed modules.
    let mut outcomes = Vec::new();
    outcomes.try_reserve_exact(plans.len()).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
    outcomes.resize_with(plans.len(), || None);
    if counters.ordinary_source_carriers {
        for (index, (plan, item)) in plans.iter().zip(&items).enumerate() {
            let HirItem::Binding(binding) = item else { continue; };
            if counters.selected_local_source_roots.as_ref().is_some_and(|selected| {
                counters.source_nodes.get(&plan.node).is_none_or(|source| !selected.contains(source))
            }) { continue; }
            let owner = SourceRootId::Definition(binding.definition_root.clone());
            let outcome = local_source::form_ordinary(
                plan, &owner, &binding.parameters, &namespace,
                counters, &artifact, &mut next_occurrence_ordinal,
            )?;
            outcomes[index] = Some((owner, outcome));
        }
    }
    if counters.ordinary_source_carriers || counters.local_source {
        for (index, (plan, item)) in plans.iter().zip(&items).enumerate() {
            let HirItem::Expression(expression) = item else { continue; };
            if counters.selected_local_source_roots.as_ref().is_some_and(|selected| {
                counters.source_nodes.get(&plan.node).is_none_or(|source| !selected.contains(source))
            }) { continue; }
            let root = expression_roots.get(expression.occurrence())
                .ok_or(HirAvailabilityError::StructuralProjection)?;
            let owner = SourceRootId::Expression(root.clone());
            let outcome = local_source::form_ordinary(
                plan, &owner, &[], &namespace, counters, &artifact, &mut next_occurrence_ordinal,
            )?;
            outcomes[index] = Some((owner, outcome));
        }
    }
    #[cfg(any(feature = "shadow", test))]
    let source_member_carriers = if counters.member_sources
        || (counters.local_source && counters.selected_local_source_roots.is_none())
    {
        let mut carriers = Vec::new();
        let mut selected_member_found = std::collections::HashSet::new();
        if let Some(selected) = &counters.selected_member_sources {
            selected_member_found.try_reserve(selected.len())
                .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        }
        // Carrier construction mutates lowering counters, so walk owned
        // declaration snapshots rather than aliasing the declaration tables.
        let role_declarations = counters.role_declarations.clone();
        let implementation_declarations = counters.implementation_declarations.clone();
        for declaration in &role_declarations {
            let Some(body) = declaration.body.as_ref() else { continue; };
            for member in &body.members {
                if member.recovered { continue; }
                let selected_member = counters.selected_member_sources.as_ref().is_some_and(|selected|
                    selected.contains(&member.id.declaration));
                if counters.selected_member_sources.is_some() && !selected_member { continue; }
                let Some(header) = member.header.as_ref() else { continue; };
                let syntax = crate::source_identity::syntax_node_at_path(parsed, &member.source_path)?;
                if syntax.kind() != member.kind
                    || crate::range_of(&syntax) != member.range
                    || syntax.text().to_string() != member.text.as_ref()
                    || counters.source_nodes.get(&syntax) != Some(&member.id.declaration)
                { return Err(HirAvailabilityError::StructuralProjection); }
                let Some(expression) = local_source::member_body_expression(&syntax)? else {
                    if selected_member { return Err(HirAvailabilityError::StructuralProjection); }
                    continue;
                };
                let owner = SourceRootId::Member(SourceMemberRootId::new(
                    artifact.clone(), identity.module().clone(),
                    declaration.id.declaration.clone(), member.id.declaration.clone(),
                    SourceMemberKind::Role,
                ));
                let plan = RootPlan { ordinal: 0, range: crate::range_of(&expression), node: expression, kind: RootPlanKind::DirectExpression };
                let outcome = local_source::form_member(
                    &plan, &owner, header, &namespace, counters, &artifact, &mut next_occurrence_ordinal,
                )?;
                carriers.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
                carriers.push((owner, outcome));
                if selected_member && !selected_member_found.insert(member.id.declaration.clone()) {
                    return Err(HirAvailabilityError::StructuralProjection);
                }
            }
        }
        for declaration in &implementation_declarations {
            let Some(body) = declaration.body.as_ref() else { continue; };
            for member in body.entries.iter().filter(|entry| entry.member.is_some()) {
                if member.recovered { continue; }
                let selected_member = counters.selected_member_sources.as_ref().is_some_and(|selected|
                    selected.contains(&member.source));
                if counters.selected_member_sources.is_some() && !selected_member { continue; }
                let Some(header) = member.header.as_ref() else { continue; };
                let path = member.source_path.as_deref().ok_or(HirAvailabilityError::StructuralProjection)?;
                let syntax = crate::source_identity::syntax_node_at_path(parsed, path)?;
                if syntax.kind() != member.kind
                    || crate::range_of(&syntax) != member.range
                    || syntax.text().to_string() != member.text.as_ref()
                    || counters.source_nodes.get(&syntax) != Some(&member.source)
                { return Err(HirAvailabilityError::StructuralProjection); }
                let Some(expression) = local_source::member_body_expression(&syntax)? else {
                    if selected_member { return Err(HirAvailabilityError::StructuralProjection); }
                    continue;
                };
                let owner = SourceRootId::Member(SourceMemberRootId::new(
                    artifact.clone(), identity.module().clone(),
                    declaration.id.declaration.clone(), member.source.clone(),
                    SourceMemberKind::Implementation,
                ));
                let plan = RootPlan { ordinal: 0, range: crate::range_of(&expression), node: expression, kind: RootPlanKind::DirectExpression };
                let outcome = local_source::form_member(
                    &plan, &owner, header, &namespace, counters, &artifact, &mut next_occurrence_ordinal,
                )?;
                carriers.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
                carriers.push((owner, outcome));
                if selected_member && !selected_member_found.insert(member.source.clone()) {
                    return Err(HirAvailabilityError::StructuralProjection);
                }
            }
        }
        if counters.selected_member_sources.as_ref().is_some_and(|selected|
            selected_member_found.len() != selected.len()) {
            return Err(HirAvailabilityError::StructuralProjection);
        }
        carriers
    } else { Vec::new() };
    #[cfg(not(any(feature = "shadow", test)))]
    let source_member_carriers: Vec<(SourceRootId, local_source::SourceCarrierOutcome)> = Vec::new();
    finalize_ordinary_admissions(
        &mut items,
        counters,
        &artifact,
        &mut next_occurrence_ordinal,
    )?;
    if let Some(selected) = &selected_ordinals {
        let retained_definitions = plans.iter().filter_map(|plan| {
            if !selected.contains(&plan.ordinal) { return None; }
            match &plan.kind { RootPlanKind::Binding(admitted) => Some(admitted.id.clone()), _ => None }
        }).collect::<std::collections::HashSet<_>>();
        let retained_errors = sink.errors.iter().filter(|error| match error.attachment() {
            HirErrorAttachment::Module => plans.iter().any(|plan| {
                selected.contains(&plan.ordinal)
                    && (error.range.start < plan.range.end && plan.range.start < error.range.end
                        || error.range.is_empty() && plan.range.start <= error.range.start && error.range.start <= plan.range.end)
            }),
            HirErrorAttachment::DirectRootItem(ordinal) => selected.contains(ordinal),
            HirErrorAttachment::Definition(id) | HirErrorAttachment::Value(id) => retained_definitions.contains(id),
        }).map(HirError::id).collect::<std::collections::HashSet<_>>();
        sink.errors.retain(|error| retained_errors.contains(&error.id()));
        sink.diagnostics.retain(|diagnostic| retained_errors.contains(&diagnostic.error()));
        let mut ordinal = 0u32;
        items.retain(|_| { let keep = selected.contains(&ordinal); ordinal += 1; keep });
        expression_roots.retain(|occurrence, _| items.iter().any(|item| matches!(item, HirItem::Expression(expression) if expression.occurrence() == occurrence)));
        let source_nodes = &counters.source_nodes;
        if let Some(source) = counters.source_identity.as_mut() {
            source.definitions.retain(|_, key| plans.iter().any(|plan| {
                selected.contains(&plan.ordinal) && source_nodes.get(&plan.node).is_some_and(|root| root == key)
            }));
            source.expressions.retain(|_, key| plans.iter().any(|plan| {
                selected.contains(&plan.ordinal) && source_nodes.get(&plan.node).is_some_and(|root| root == key)
            }));
        }
    }
    let source_carriers: Vec<_> = outcomes.into_iter().flatten().collect();
    let mut source_carrier_indices = HashMap::new();
    source_carrier_indices.try_reserve(source_carriers.len()).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
    for (index, (owner, _)) in source_carriers.iter().enumerate() {
        source_carrier_indices.insert(owner.clone(), index);
    }
    let mut source_member_carrier_indices = HashMap::new();
    source_member_carrier_indices.try_reserve(source_member_carriers.len()).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
    for (index, (owner, _)) in source_member_carriers.iter().enumerate() {
        source_member_carrier_indices.insert(owner.clone(), index);
    }
    if let Some(binding) = imports.caller_evidence.as_ref() {
        let admitted = counters.source_identity.as_ref().is_some_and(|source| {
            source.definitions.values().any(|key| key == &binding.declaration)
        });
        if !admitted {
            return Err(HirAvailabilityError::CallerEvidenceNotDeclaration);
        }
    }
    Ok(HirModule {
        expression_roots,
        source_carriers,
        source_carrier_indices,
        source_member_carriers,
        source_member_carrier_indices,
        artifact,
        caller_evidence: imports.caller_evidence,
        source_imports: imports.source_imports,
        source_identity: counters.source_identity.take(),
        #[cfg(any(feature = "shadow", test))]
        captured_source: None,
        source_parsed: (counters.local_source || counters.member_sources).then(|| parsed.clone()),
        local_sources: std::mem::take(&mut counters.local_sources),
        #[cfg(any(feature = "shadow", test))]
        effect_declarations: std::mem::take(&mut counters.effect_declarations),
        #[cfg(any(feature = "shadow", test))]
        role_declarations: std::mem::take(&mut counters.role_declarations),
        #[cfg(any(feature = "shadow", test))]
        implementation_declarations: std::mem::take(&mut counters.implementation_declarations),
        identity,
        source_revision: parsed.revision(),
        items,
        errors: sink.errors,
        diagnostics: sink.diagnostics,
        definition_root_allocation_bytes: counters.definition_root_allocation_bytes,
        definition_root_def_id_clone_bytes: counters.definition_root_def_id_clone_bytes,
    })
}

fn next_occurrence(
    artifact: &Arc<HirArtifactToken>,
    ordinal: &mut u32,
) -> Result<HirOccurrenceId, HirAvailabilityError> {
    let current = *ordinal;
    *ordinal = ordinal
        .checked_add(1)
        .ok_or(HirAvailabilityError::IdentityExhausted)?;
    Ok(HirOccurrenceId::new(artifact.clone(), current))
}

#[derive(Default)]
struct LoweringCounters {
    ordinary_source_carriers: bool,
    local_source: bool,
    member_sources: bool,
    selected_member_sources: Option<std::collections::HashSet<yu_syntax::SourceNodeKey>>,
    selected_local_source_roots: Option<std::collections::HashSet<yu_syntax::SourceNodeKey>>,
    local_sources: HashMap<DefinitionRootId, local_source::LocalSource>,
    #[cfg(any(feature = "shadow", test))]
    effect_declarations: Vec<source_annotation::SourceEffectDeclaration>,
    #[cfg(any(feature = "shadow", test))]
    role_declarations: Vec<source_role::SourceRoleDeclaration>,
    #[cfg(any(feature = "shadow", test))]
    implementation_declarations: Vec<source_impl::SourceImplementationDeclaration>,
    effect_namespace: HashMap<String, Vec<source_annotation::SourceEffectId>>,
    operation_namespace: HashMap<
        (source_annotation::SourceEffectId, Box<str>),
        Vec<Arc<source_annotation::SourceOperationDeclaration>>,
    >,
    shadow_applications: bool,
    source_identity: Option<crate::source_identity::HirSourceIdentity>,
    source_nodes: HashMap<SyntaxNode, yu_syntax::SourceNodeKey>,
    /// Exact parser-associated dynamic operators retained for source carriers.
    source_operator_uses: HashMap<Range<usize>, crate::HirOperator>,
    /// Exact parser-associated expression trees indexed by each operator-use range.
    source_associated_chains: HashMap<Range<usize>, Arc<crate::HirExpr>>,
    recovery_visits: usize,
    syntax_emissions: usize,
    copied_spelling_bytes: usize,
    definition_root_allocation_bytes: usize,
    definition_root_def_id_clone_bytes: usize,
    pending_ordinary_admissions: Vec<PendingOrdinaryAdmission>,
    aggregate_error_references: usize,
    aggregate_error_reference_bytes: usize,
    ordinary_admission_item_visits: usize,
}

fn retain_associated_operator_uses(
    expression: &HirExpr,
    uses: &mut HashMap<Range<usize>, crate::HirOperator>,
) -> Result<(), HirAvailabilityError> {
    match expression {
        HirExpr::Apply { operator, operands, .. } => {
            uses.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
            if uses.insert(operator.range().clone(), operator.clone()).is_some() {
                return Err(HirAvailabilityError::StructuralProjection);
            }
            for operand in operands.iter() { retain_associated_operator_uses(operand, uses)?; }
        }
        HirExpr::Value { children, .. } | HirExpr::Error { children, .. } => {
            for child in children { retain_associated_operator_uses(child, uses)?; }
        }
    }
    Ok(())
}

fn retain_associated_operator_chains(
    expression: &HirExpr,
    tree: &Arc<HirExpr>,
    chains: &mut HashMap<Range<usize>, Arc<HirExpr>>,
) -> Result<(), HirAvailabilityError> {
    let mut pending = Vec::new();
    pending.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
    pending.push(expression);
    while let Some(expression) = pending.pop() {
        match expression {
            HirExpr::Apply { operator, operands, .. } => {
                chains.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
                if chains.insert(operator.range().clone(), Arc::clone(tree)).is_some() {
                    return Err(HirAvailabilityError::StructuralProjection);
                }
                pending.try_reserve(operands.len()).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
                for operand in operands.iter() {
                    pending.push(operand);
                }
            }
            HirExpr::Value { children, .. } | HirExpr::Error { children, .. } => {
                pending.try_reserve(children.len()).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
                for child in children {
                    pending.push(child);
                }
            }
        }
    }
    Ok(())
}

struct PendingOrdinaryAdmission {
    root: HirOccurrenceId,
    owner_item_index: usize,
    nodes: Vec<PendingProjectionNode>,
}

struct PendingProjectionNode {
    kind: PendingProjectionKind,
    source_atom: Option<crate::OwnedAtom>,
    range: Range<usize>,
    key: yu_syntax::SourceNodeKey,
    children: Vec<usize>,
    atom: Option<ResolvedExpr>,
    staged_error: Option<(HirErrorKind, Range<usize>)>,
    error: Option<HirErrorId>,
    descendant_errors: usize,
}

#[derive(Clone, Copy)]
enum PendingProjectionKind { Apply(SyntaxKind), Group, Atom }

fn lower_ordinary_admission(
    parsed: &ParsedFile,
    chain: &SyntaxNode,
    namespace: &ModuleNamespace,
    causal_errors: &[HirErrorId],
    counters: &mut LoweringCounters,
    root_occurrence: HirOccurrenceId,
    owner_item_index: usize,
    scope: &ScopeStack,
) -> Result<Option<ResolvedExpr>, HirAvailabilityError> {
    if !causal_errors.is_empty() { return Ok(None); }
    let associated = associate_chain_owned_with_sources(parsed, chain.clone())
        .map_err(|error| match error {
            AssociationError::ExactOperatorEnvironment => HirAvailabilityError::ExactOperatorEnvironment,
            AssociationError::StructuralInvariant => HirAvailabilityError::StructuralProjection,
            AssociationError::Allocation => HirAvailabilityError::IdentityExhausted,
        })?;
    let (hir, provenance, _) = associated.into_projection_parts();
    let mut nodes = Vec::new();
    let mut tasks = Vec::new();
    tasks.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
    tasks.push((&hir, &provenance, None::<usize>));
    while let Some((expression, source_shape, parent)) = tasks.pop() {
        let (kind, range, children) = match expression {
            HirExpr::Value { kind, range, children } => (*kind, range.clone(), children.as_slice()),
            HirExpr::Error { .. } | HirExpr::Apply { .. } => return Ok(None),
        };
        let AssociationProvenance::Node { source, children: source_children } = source_shape else {
            return Ok(None);
        };
        if source.kind() != kind || children.len() != source_children.len() { return Ok(None); }
        let projection_kind = match kind {
            SyntaxKind::IdentifierExpression | SyntaxKind::IntegerLiteral if children.is_empty() => PendingProjectionKind::Atom,
            SyntaxKind::ParenthesizedExpression if children.len() == 1 => {
                if has_direct_comma_or_separator(source) { return Ok(None); }
                PendingProjectionKind::Group
            }
            SyntaxKind::MlArgument | SyntaxKind::CallTail if children.len() == 2 => {
                if kind == SyntaxKind::CallTail && has_direct_comma_or_separator(source) { return Ok(None); }
                PendingProjectionKind::Apply(kind)
            }
            _ => return Ok(None),
        };
        let source_atom = if matches!(projection_kind, PendingProjectionKind::Atom) {
            let mut tokens = source.children_with_tokens().filter_map(|element| element.into_token())
                .filter(|token| matches!(token.kind(), SyntaxKind::Identifier | SyntaxKind::Integer));
            let Some(token) = tokens.next() else { return Ok(None); };
            if tokens.next().is_some() { return Ok(None); }
            Some(crate::OwnedAtom { source: source.clone(), kind, spelling: token.text().to_owned(), range: crate::range_of_token(&token) })
        } else { None };
        let key = counters.source_nodes.get(source).cloned().ok_or(HirAvailabilityError::StructuralProjection)?;
        let index = nodes.len();
        index.checked_add(1).ok_or(HirAvailabilityError::IdentityExhausted)?;
        nodes.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        nodes.push(PendingProjectionNode { kind: projection_kind, source_atom, range, key, children: Vec::new(), atom: None, staged_error: None, error: None, descendant_errors: 0 });
        if let Some(parent) = parent {
            let parent_node = nodes.get_mut(parent).ok_or(HirAvailabilityError::StructuralProjection)?;
            parent_node.children.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
            parent_node.children.push(index);
        }
        for (child, child_source) in children.iter().zip(source_children).rev() {
            tasks.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
            tasks.push((child, child_source, Some(index)));
        }
    }
    if nodes.is_empty() { return Ok(None); }

    // Preflight has fully accepted the source grammar before any operand is resolved.
    // Diagnostics are only staged here; `lower_plan` assigns dense IDs after the
    // existing duplicate-definition event at its established scheduling seam.
    for node in &mut nodes {
        if !matches!(node.kind, PendingProjectionKind::Atom) { continue; }
        let atom = node.source_atom.take().ok_or(HirAvailabilityError::StructuralProjection)?;
        let lowered = lower_leaf_with_identity(atom, namespace, counters, root_occurrence.clone(), scope, false)?;
        let SimpleChainLowering::Resolved { expression, semantic_error } = lowered else { return Ok(None); };
        node.staged_error = semantic_error;
        node.atom = Some(expression);
    }
    counters.pending_ordinary_admissions.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
    counters.pending_ordinary_admissions.push(PendingOrdinaryAdmission { root: root_occurrence.clone(), owner_item_index, nodes });
    Ok(Some(ResolvedExpr::Error { occurrence: root_occurrence, errors: Vec::new().into_boxed_slice(), range: range_of(chain) }))
}

fn emit_ordinary_admission_errors(
    counters: &mut LoweringCounters,
    admission_start: usize,
    owner_item_index: usize,
    id: &Arc<DefId>,
    sink: &mut ErrorSink,
) -> Result<(), HirAvailabilityError> {
    let admissions = counters.pending_ordinary_admissions.get_mut(admission_start..)
        .ok_or(HirAvailabilityError::StructuralProjection)?;
    for admission in admissions {
        if admission.owner_item_index != owner_item_index { return Err(HirAvailabilityError::StructuralProjection); }
        for node in &mut admission.nodes {
            let Some((kind, range)) = node.staged_error.take() else { continue; };
            node.error = Some(sink.lowering(kind, HirErrorAttachment::Value((**id).clone()), range)?);
        }
    }
    Ok(())
}

fn has_direct_comma_or_separator(source: &SyntaxNode) -> bool {
    source.children_with_tokens().any(|element| matches!(element.kind(), SyntaxKind::Comma | SyntaxKind::ExpressionDelimitedSeparator))
}

fn finalize_ordinary_admissions(
    items: &mut [HirItem],
    counters: &mut LoweringCounters,
    artifact: &Arc<HirArtifactToken>,
    next_ordinal: &mut u32,
) -> Result<(), HirAvailabilityError> {
    if counters.pending_ordinary_admissions.is_empty() {
        return Ok(());
    }
    let identity = counters.source_identity.as_mut().ok_or(HirAvailabilityError::StructuralProjection)?;
    for mut admission in counters.pending_ordinary_admissions.drain(..) {
        let node_count = admission.nodes.len();
        for index in (0..node_count).rev() {
            let child_errors = admission.nodes[index].children.iter().try_fold(0usize, |sum, child| {
                sum.checked_add(admission.nodes.get(*child)?.descendant_errors)
            }).ok_or(HirAvailabilityError::IdentityExhausted)?;
            let own_error = usize::from(admission.nodes[index].error.is_some());
            admission.nodes[index].descendant_errors = match admission.nodes[index].kind {
                PendingProjectionKind::Atom => own_error,
                PendingProjectionKind::Group => child_errors,
                PendingProjectionKind::Apply(_) => child_errors,
            };
        }

        let mut occurrences = Vec::new();
        occurrences.try_reserve_exact(node_count).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        let mut stage = identity.empty_stage();
        let existing_root = validate_admission_root_mapping(identity, &admission.root, &admission.nodes[0].key)?;
        let staged_count = node_count.checked_sub(usize::from(existing_root.is_some()))
            .ok_or(HirAvailabilityError::IdentityExhausted)?;
        stage.occurrences.try_reserve(staged_count)
            .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        for (index, node) in admission.nodes.iter().enumerate() {
            let occurrence = if index == 0 {
                admission.root.clone()
            } else {
                next_occurrence(artifact, next_ordinal)?
            };
            if index != 0 || existing_root.is_none() {
                if !stage.record_unique_occurrence(occurrence.clone(), node.key.clone()) {
                    return Err(HirAvailabilityError::InconsistentIdentity);
                }
            }
            occurrences.push(occurrence);
        }

        let mut lowered: Vec<Option<ResolvedExpr>> = Vec::new();
        lowered.try_reserve_exact(node_count).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        lowered.resize_with(node_count, || None);
        for index in (0..node_count).rev() {
            let occurrence = occurrences[index].clone();
            let expression = match admission.nodes[index].kind {
                PendingProjectionKind::Atom => {
                    let mut expression = admission.nodes[index].atom.take()
                        .ok_or(HirAvailabilityError::StructuralProjection)?;
                    set_expression_occurrence(&mut expression, occurrence)?;
                    expression
                }
                PendingProjectionKind::Group => {
                    let child = *admission.nodes[index].children.first()
                        .ok_or(HirAvailabilityError::StructuralProjection)?;
                    if admission.nodes[index].children.len() != 1 {
                        return Err(HirAvailabilityError::StructuralProjection);
                    }
                    let inner = lowered.get_mut(child).and_then(Option::take)
                        .ok_or(HirAvailabilityError::StructuralProjection)?;
                    ResolvedExpr::Group {
                        occurrence,
                        inner: try_box(inner)?,
                        range: admission.nodes[index].range.clone(),
                    }
                }
                PendingProjectionKind::Apply(source_form) => {
                    if admission.nodes[index].children.len() != 2 {
                        return Err(HirAvailabilityError::StructuralProjection);
                    }
                    let [callee_index, argument_index] = admission.nodes[index].children.as_slice() else {
                        return Err(HirAvailabilityError::StructuralProjection);
                    };
                    let count = admission.nodes[index].descendant_errors;
                    let bytes = count.checked_mul(std::mem::size_of::<HirErrorId>())
                        .ok_or(HirAvailabilityError::IdentityExhausted)?;
                    counters.aggregate_error_references = counters.aggregate_error_references
                        .checked_add(count).ok_or(HirAvailabilityError::IdentityExhausted)?;
                    counters.aggregate_error_reference_bytes = counters.aggregate_error_reference_bytes
                        .checked_add(bytes).ok_or(HirAvailabilityError::IdentityExhausted)?;
                    let callee_expr = lowered.get(*callee_index).and_then(Option::as_ref)
                        .ok_or(HirAvailabilityError::StructuralProjection)?;
                    let argument_expr = lowered.get(*argument_index).and_then(Option::as_ref)
                        .ok_or(HirAvailabilityError::StructuralProjection)?;
                    let errors = build_projection_error_list(
                        [(*callee_index, callee_expr), (*argument_index, argument_expr)],
                        &admission.nodes,
                        count,
                    )?;
                    let callee = lowered.get_mut(*callee_index).and_then(Option::take)
                        .ok_or(HirAvailabilityError::StructuralProjection)?;
                    let argument = lowered.get_mut(*argument_index).and_then(Option::take)
                        .ok_or(HirAvailabilityError::StructuralProjection)?;
                    ResolvedExpr::Apply {
                        occurrence,
                        source_form,
                        callee: try_box(callee)?,
                        argument: try_box(argument)?,
                        errors,
                        range: admission.nodes[index].range.clone(),
                    }
                }
            };
            lowered[index] = Some(expression);
        }
        let root_expression = lowered.get_mut(0).and_then(Option::take)
            .ok_or(HirAvailabilityError::StructuralProjection)?;
        let next_item_visits = counters.ordinary_admission_item_visits
            .checked_add(1).ok_or(HirAvailabilityError::IdentityExhausted)?;
        let item = items.get_mut(admission.owner_item_index)
            .ok_or(HirAvailabilityError::StructuralProjection)?;
        let HirItem::Binding(binding) = item else {
            return Err(HirAvailabilityError::StructuralProjection);
        };
        if !admission_root_placeholder_matches(&binding.value, &admission.root) {
            return Err(HirAvailabilityError::StructuralProjection);
        }
        identity.append_stage(stage)?;
        replace_validated_admission_root(&mut binding.value, &admission.root, root_expression);
        counters.ordinary_admission_item_visits = next_item_visits;
        binding.evaluation_class = evaluation_class(&binding.value);
    }
    Ok(())
}

fn try_box<T>(value: T) -> Result<Box<T>, HirAvailabilityError> {
    let layout = Layout::new::<T>();
    if layout.size() == 0 {
        return Ok(Box::new(value));
    }
    let pointer = std::ptr::NonNull::new(unsafe { alloc(layout).cast::<T>() })
        .ok_or(HirAvailabilityError::IdentityExhausted)?;
    // SAFETY: `pointer` is a unique allocation from the global allocator with
    // exactly `layout`; it is initialized once and transferred to `Box`.
    unsafe {
        pointer.as_ptr().write(value);
        Ok(Box::from_raw(pointer.as_ptr()))
    }
}

fn validate_admission_root_mapping<'a>(
    identity: &'a crate::source_identity::HirSourceIdentity,
    root: &HirOccurrenceId,
    key: &yu_syntax::SourceNodeKey,
) -> Result<Option<&'a yu_syntax::SourceNodeKey>, HirAvailabilityError> {
    match identity.occurrences.get(root) {
        Some(existing) if existing != key => Err(HirAvailabilityError::InconsistentIdentity),
        existing => Ok(existing),
    }
}

fn build_projection_error_list(
    children: [(usize, &ResolvedExpr); 2],
    nodes: &[PendingProjectionNode],
    expected: usize,
) -> Result<Box<[HirErrorId]>, HirAvailabilityError> {
    if expected == 0 { return Ok(Box::new([])); }
    let layout = Layout::array::<HirErrorId>(expected)
        .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
    let raw = unsafe { alloc(layout).cast::<HirErrorId>() };
    if raw.is_null() { return Err(HirAvailabilityError::IdentityExhausted); }
    let mut written = 0usize;
    let result = children.into_iter().try_for_each(|(index, expr)| {
        append_projection_errors(index, expr, nodes, raw, expected, &mut written)
    });
    if result.is_err() || written != expected {
        // HirErrorId is Copy and no value owns a destructor in this raw buffer.
        unsafe { std::alloc::dealloc(raw.cast(), layout); }
        return result.and(Err(HirAvailabilityError::StructuralProjection));
    }
    // SAFETY: every slot in the exact-sized allocation has been initialized by
    // append_projection_errors, and Box now owns the matching global allocation.
    Ok(unsafe { Box::from_raw(std::ptr::slice_from_raw_parts_mut(raw, expected)) })
}

fn append_projection_errors(
    root: usize,
    expression: &ResolvedExpr,
    nodes: &[PendingProjectionNode],
    output: *mut HirErrorId,
    capacity: usize,
    written: &mut usize,
) -> Result<(), HirAvailabilityError> {
    let node = nodes.get(root).ok_or(HirAvailabilityError::StructuralProjection)?;
    match (&node.kind, expression) {
        (PendingProjectionKind::Atom, ResolvedExpr::Integer { .. } | ResolvedExpr::Name { .. }) => {
            if let Some(error) = node.error {
                if *written >= capacity { return Err(HirAvailabilityError::StructuralProjection); }
                unsafe { output.add(*written).write(error); }
                *written = written.checked_add(1).ok_or(HirAvailabilityError::IdentityExhausted)?;
            }
        }
        (PendingProjectionKind::Group, ResolvedExpr::Group { inner, .. }) => {
            let [child] = node.children.as_slice() else { return Err(HirAvailabilityError::StructuralProjection); };
            append_projection_errors(*child, inner.as_ref(), nodes, output, capacity, written)?;
        }
        (PendingProjectionKind::Apply(_), ResolvedExpr::Apply { errors, .. }) => {
            let end = written.checked_add(errors.len()).ok_or(HirAvailabilityError::IdentityExhausted)?;
            if end > capacity { return Err(HirAvailabilityError::StructuralProjection); }
            unsafe { std::ptr::copy_nonoverlapping(errors.as_ptr(), output.add(*written), errors.len()); }
            *written = end;
        }
        _ => return Err(HirAvailabilityError::StructuralProjection),
    }
    Ok(())
}

fn set_expression_occurrence(
    expression: &mut ResolvedExpr,
    occurrence: HirOccurrenceId,
) -> Result<(), HirAvailabilityError> {
    match expression {
        ResolvedExpr::Integer { occurrence: current, .. }
        | ResolvedExpr::Name { occurrence: current, .. } => *current = occurrence,
        _ => return Err(HirAvailabilityError::StructuralProjection),
    }
    Ok(())
}

fn admission_root_placeholder_matches(
    expression: &ResolvedExpr,
    target: &HirOccurrenceId,
) -> bool {
    let mut current = expression;
    loop {
        if current.occurrence() == target {
            return matches!(current, ResolvedExpr::Error { errors, .. } if errors.is_empty());
        }
        match current {
            ResolvedExpr::Lambda { body, .. } => current = body,
            _ => return false,
        }
    }
}

fn replace_validated_admission_root(
    expression: &mut ResolvedExpr,
    target: &HirOccurrenceId,
    replacement: ResolvedExpr,
) {
    let mut current = expression;
    loop {
        if current.occurrence() == target {
            *current = replacement;
            return;
        }
        match current {
            ResolvedExpr::Lambda { body, .. } => current = body,
            _ => unreachable!("validated admission root path changed"),
        }
    }
}

#[derive(Default)]
struct ScopeStack {
    parameters: Vec<HirParameter>,
}

#[derive(Clone, Copy)]
struct ScopeDepthGuard(usize);

impl ScopeStack {
    fn push_parameter(&mut self, parameter: HirParameter) -> ScopeDepthGuard {
        let depth = ScopeDepthGuard(self.parameters.len());
        self.parameters.push(parameter);
        depth
    }

    fn root_guard(&self) -> ScopeDepthGuard {
        ScopeDepthGuard(self.parameters.len())
    }

    fn restore(&mut self, guard: ScopeDepthGuard) {
        self.parameters.truncate(guard.0);
    }

    fn parameter(&self, spelling: &str) -> Option<&HirParameter> {
        self.parameters
            .iter()
            .rev()
            .find(|parameter| parameter.name.spelling == spelling)
    }
}

struct RecoveryPartition {
    module: Vec<usize>,
    roots: Vec<Vec<usize>>,
}

#[derive(Default)]
struct RootErrors {
    item: Vec<HirErrorId>,
    value: Vec<HirErrorId>,
}

fn partition_recoveries(
    recoveries: &[StructuralRecovery],
    root_count: usize,
    counters: &mut LoweringCounters,
) -> Result<RecoveryPartition, HirAvailabilityError> {
    let mut partition = RecoveryPartition {
        module: Vec::new(),
        roots: (0..root_count).map(|_| Vec::new()).collect(),
    };
    for (index, recovery) in recoveries.iter().enumerate() {
        counters.recovery_visits += 1;
        match recovery.direct_root_ordinal() {
            None => partition.module.push(index),
            Some(ordinal) => {
                let root = usize::try_from(ordinal)
                    .map_err(|_| HirAvailabilityError::StructuralProjection)?;
                let bucket = partition
                    .roots
                    .get_mut(root)
                    .ok_or(HirAvailabilityError::StructuralProjection)?;
                bucket.push(index);
            }
        }
    }
    Ok(partition)
}

fn emit_structural_errors(
    recoveries: &[StructuralRecovery],
    partition: &RecoveryPartition,
    plans: &[RootPlan],
    sink: &mut ErrorSink,
    counters: &mut LoweringCounters,
) -> Result<Vec<RootErrors>, HirAvailabilityError> {
    let mut recovery_errors = Vec::with_capacity(recoveries.len());
    for recovery in recoveries {
        let attachment = match recovery.direct_root_ordinal() {
            None => HirErrorAttachment::Module,
            Some(ordinal) => {
                let root = usize::try_from(ordinal)
                    .map_err(|_| HirAvailabilityError::StructuralProjection)?;
                plans
                    .get(root)
                    .ok_or(HirAvailabilityError::StructuralProjection)?
                    .recovery_attachment(recovery)
            }
        };
        recovery_errors.push(sink.syntax(recovery, attachment)?);
        counters.syntax_emissions += 1;
    }

    let mut roots = (0..plans.len())
        .map(|_| RootErrors::default())
        .collect::<Vec<_>>();
    for (root, indices) in partition.roots.iter().enumerate() {
        for &index in indices {
            let recovery = recoveries
                .get(index)
                .ok_or(HirAvailabilityError::StructuralProjection)?;
            let attachment = plans[root].recovery_attachment(recovery);
            let error = *recovery_errors
                .get(index)
                .ok_or(HirAvailabilityError::StructuralProjection)?;
            match attachment {
                HirErrorAttachment::DirectRootItem(_) => roots[root].item.push(error),
                HirErrorAttachment::Value(_) => roots[root].value.push(error),
                HirErrorAttachment::Module | HirErrorAttachment::Definition(_) => {}
            }
        }
    }
    if partition
        .module
        .iter()
        .any(|&index| index >= recovery_errors.len())
    {
        return Err(HirAvailabilityError::StructuralProjection);
    }
    Ok(roots)
}

#[derive(Clone)]
struct RootPlan {
    ordinal: u32,
    node: SyntaxNode,
    range: Range<usize>,
    kind: RootPlanKind,
}

#[derive(Clone)]
enum RootPlanKind {
    Import,
    Binding(Admitted),
    DirectExpression,
    Unsupported(HirErrorKind),
}

#[derive(Clone)]
struct Admitted {
    id: Arc<DefId>,
    visibility: HirVisibility,
    name: HirName,
    parameters: Vec<AdmittedParameter>,
}

#[derive(Clone)]
struct AdmittedParameter {
    name: HirName,
    source: Option<yu_syntax::SourceNodeKey>,
    annotation: Option<SyntaxNode>,
    unit_pattern: bool,
}

impl RootPlan {
    fn recovery_attachment(&self, recovery: &StructuralRecovery) -> HirErrorAttachment {
        match &self.kind {
            RootPlanKind::Binding(admitted) => {
                if recovery.path().contains(&SyntaxKind::BindingBody) {
                    HirErrorAttachment::Value((*admitted.id).clone())
                } else {
                    HirErrorAttachment::Definition((*admitted.id).clone())
                }
            }
            RootPlanKind::Import | RootPlanKind::DirectExpression | RootPlanKind::Unsupported(_) => {
                HirErrorAttachment::DirectRootItem(self.ordinal)
            }
        }
    }
}

fn plan_root(
    node: SyntaxNode,
    ordinal: u32,
    identity: &ModuleIdentity,
    counters: &mut LoweringCounters,
) -> Result<RootPlan, HirAvailabilityError> {
    let range = range_of(&node);
    if node.kind() == SyntaxKind::OperatorChain {
        return Ok(RootPlan {
            ordinal,
            node,
            range,
            kind: RootPlanKind::DirectExpression,
        });
    }
    if node.kind() != SyntaxKind::BindingStatement {
        return Ok(RootPlan {
            ordinal,
            node,
            range,
            kind: RootPlanKind::Unsupported(HirErrorKind::UnsupportedItem),
        });
    }
    let Some((visibility, name, parameters)) = plain_binding_header(&node, counters) else {
        return Ok(RootPlan {
            ordinal,
            node,
            range,
            kind: RootPlanKind::Unsupported(HirErrorKind::UnsupportedTarget),
        });
    };
    counters.copied_spelling_bytes += name.spelling.len();
    let same_name_ordinal = 0; // assigned after all direct-root headers are known
    let id = Arc::new(DefId {
        module: identity.module.clone(),
        spelling: name.spelling.clone().into_boxed_str(),
        same_name_ordinal,
    });
    Ok(RootPlan {
        ordinal,
        node,
        range,
        kind: RootPlanKind::Binding(Admitted {
            id,
            visibility,
            name,
            parameters,
        }),
    })
}

#[derive(Clone, Debug)]
pub(super) enum ModuleNameResolution {
    Local(DefId),
    Imported(source_exports::SourceExportId),
    #[cfg(any(feature = "shadow", test))]
    ImportedOperation(source_exports::SourceOperationPathImport),
    Ambiguous,
}

pub(super) type ModuleNamespace = HashMap<String, ModuleNameResolution>;

fn namespace(
    plans: &mut [RootPlan],
    imports: Option<&source_exports::SourceImportEnvironment>,
) -> Result<ModuleNamespace, HirAvailabilityError> {
    let mut seen = HashMap::<String, u32>::new();
    let mut local = HashMap::<String, Vec<DefId>>::new();
    for plan in plans {
        let RootPlanKind::Binding(admitted) = &mut plan.kind else {
            continue;
        };
        let ordinal = seen.entry(admitted.name.spelling.clone()).or_default();
        let id = Arc::new(DefId {
            module: admitted.id.module.clone(),
            spelling: admitted.id.spelling.clone(),
            same_name_ordinal: *ordinal,
        });
        *ordinal = ordinal
            .checked_add(1)
            .ok_or(HirAvailabilityError::IdentityExhausted)?;
        admitted.id = id.clone();
        local
            .entry(admitted.name.spelling.clone())
            .or_default()
            .push((*id).clone());
    }
    let mut namespace = HashMap::new();
    namespace.try_reserve(local.len()).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
    for (name, definitions) in local {
        let resolution = if definitions.len() == 1 {
            ModuleNameResolution::Local(definitions[0].clone())
        } else {
            ModuleNameResolution::Ambiguous
        };
        namespace.insert(name, resolution);
    }
    if let Some(imports) = imports {
        namespace.try_reserve(imports.names().len()).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        for (name, binding) in imports.names() {
            if namespace.contains_key(name.as_ref()) { continue; }
            let resolution = match binding {
                source_exports::SourceImportBinding::Resolved(export) => {
                    ModuleNameResolution::Imported(export.identity())
                }
                source_exports::SourceImportBinding::Ambiguous => ModuleNameResolution::Ambiguous,
            };
            namespace.insert(name.to_string(), resolution);
        }
        #[cfg(any(feature = "shadow", test))]
        for (path, operation) in imports.operation_paths() {
            namespace.insert(path.to_string(), ModuleNameResolution::ImportedOperation(operation.clone()));
        }
    }
    Ok(namespace)
}

fn lower_plan(
    plan: &RootPlan,
    parsed: &ParsedFile,
    namespace: &ModuleNamespace,
    mut item_errors: Vec<HirErrorId>,
    value_errors: Vec<HirErrorId>,
    sink: &mut ErrorSink,
    counters: &mut LoweringCounters,
    occurrence: HirOccurrenceId,
    definition_root: Option<DefinitionRootId>,
    artifact: &Arc<HirArtifactToken>,
    next_occurrence_ordinal: &mut u32,
    scope: &mut ScopeStack,
) -> Result<HirItem, HirAvailabilityError> {
    let RootPlanKind::Binding(admitted) = &plan.kind else {
        return match &plan.kind {
            RootPlanKind::Import if item_errors.is_empty() && value_errors.is_empty() => {
                Ok(HirItem::Import { range: plan.range.clone() })
            }
            RootPlanKind::Import => {
                item_errors.extend(value_errors);
                Ok(HirItem::Error { errors: item_errors.into_boxed_slice(), range: plan.range.clone() })
            }
            RootPlanKind::DirectExpression => lower_direct_root_expression(
                plan,
                parsed,
                namespace,
                item_errors,
                sink,
                counters,
                occurrence,
                scope,
                next_occurrence_ordinal,
            ),
            RootPlanKind::Unsupported(kind) => {
                item_errors.push(sink.lowering(
                    *kind,
                    HirErrorAttachment::DirectRootItem(plan.ordinal),
                    plan.range.clone(),
                )?);
                Ok(HirItem::Error {
                    errors: item_errors.into_boxed_slice(),
                    range: plan.range.clone(),
                })
            }
            RootPlanKind::Binding(_) => unreachable!("binding plan matched above"),
        };
    };
    let id = admitted.id.clone();
    let definition_root = definition_root.expect("admitted binding has a definition root");
    #[cfg(any(feature = "shadow", test))]
    if (counters.shadow_applications || counters.local_source) && admitted.parameters.len() > 127 {
        return Err(HirAvailabilityError::StructuralProjection);
    }
    let mut parameters = Vec::with_capacity(admitted.parameters.len());
    for (ordinal, admitted) in admitted.parameters.iter().enumerate() {
        let ordinal =
            u32::try_from(ordinal).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        let parameter = HirParameter {
            id: HirParameterId::new(definition_root.clone(), ordinal),
            name: admitted.name.clone(),
            range: admitted.name.range.clone(),
            unit_pattern: admitted.unit_pattern,
        };
        if let (Some(source), Some(key)) = (&mut counters.source_identity, &admitted.source) {
            source.record_parameter(parameter.id.clone(), key.clone());
        }
        parameters.push(parameter);
    }
    let parameters = parameters.into_boxed_slice();
    #[cfg(any(feature = "shadow", test))]
    let selected_for_local_source = counters
        .selected_local_source_roots
        .as_ref()
        .is_none_or(|selected| counters.source_nodes.get(&plan.node).is_some_and(|source| selected.contains(source)));
    #[cfg(any(feature = "shadow", test))]
    let simple_body_projection = if counters.local_source && selected_for_local_source {
        let (carrier, projection) = local_source::form(
            plan,
            &SourceRootId::Definition(definition_root.clone()),
            &parameters,
            &[],
            None,
            namespace,
            counters,
            artifact,
            next_occurrence_ordinal,
        )?;
        counters
            .local_sources
            .try_reserve(1)
            .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        counters
            .local_sources
            .insert(definition_root.clone(), carrier);
        Some(projection)
    } else {
        None
    };
    let mut lambda_occurrences = Vec::with_capacity(parameters.len());
    for ordinal in 0..parameters.len() {
        lambda_occurrences.push(if ordinal == 0 {
            occurrence.clone()
        } else {
            next_occurrence(artifact, next_occurrence_ordinal)?
        });
    }
    let body_occurrence = if parameters.is_empty() {
        occurrence
    } else {
        next_occurrence(artifact, next_occurrence_ordinal)?
    };
    let guard = scope.root_guard();
    for parameter in &parameters {
        if !parameter.unit_pattern { scope.push_parameter(parameter.clone()); }
    }
    let owner_item_index = usize::try_from(plan.ordinal)
        .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
    let admission_start = counters.pending_ordinary_admissions.len();
    let lowered = lower_body(
        plan,
        parsed,
        namespace,
        &id,
        value_errors,
        sink,
        counters,
        body_occurrence,
        scope,
        next_occurrence_ordinal,
        128 - parameters.len(),
        #[cfg(any(feature = "shadow", test))]
        simple_body_projection,
    );
    scope.restore(guard);
    let (value, body_semantic_error) = lowered?;
    if id.same_name_ordinal > 0 {
        sink.lowering(
            HirErrorKind::DuplicateDefinition,
            HirErrorAttachment::Definition((*id).clone()),
            admitted.name.range.clone(),
        )?;
    }
    emit_ordinary_admission_errors(counters, admission_start, owner_item_index, &id, sink)?;
    if let Some((kind, range)) = body_semantic_error {
        sink.lowering(kind, HirErrorAttachment::Value((*id).clone()), range)?;
    }
    let mut value = value;
    for (parameter, occurrence) in parameters.iter().zip(lambda_occurrences).rev() {
        value = ResolvedExpr::Lambda {
            occurrence,
            parameter: parameter.id.clone(),
            range: plan.range.clone(),
            body: Box::new(value),
        };
    }
    let evaluation_class = evaluation_class(&value);
    Ok(HirItem::Binding(HirBinding {
        id,
        definition_root,
        visibility: admitted.visibility,
        name: admitted.name.clone(),
        parameters,
        evaluation_class,
        value,
        range: plan.range.clone(),
    }))
}

fn lower_direct_root_expression(
    plan: &RootPlan,
    parsed: &ParsedFile,
    namespace: &ModuleNamespace,
    mut causal_errors: Vec<HirErrorId>,
    sink: &mut ErrorSink,
    counters: &mut LoweringCounters,
    occurrence: HirOccurrenceId,
    scope: &ScopeStack,
    _next_occurrence_ordinal: &mut u32,
) -> Result<HirItem, HirAvailabilityError> {
    if !causal_errors.is_empty() {
        return Ok(HirItem::Expression(ResolvedExpr::Error {
            occurrence,
            errors: causal_errors.into_boxed_slice(),
            range: plan.range.clone(),
        }));
    }
    #[cfg(any(feature = "shadow", test))]
    if counters.shadow_applications {
        if let Some(expression) = lower_shadow_application(
            parsed,
            &plan.node,
            namespace,
            counters,
            occurrence.clone(),
            scope,
            _next_occurrence_ordinal,
            sink,
            HirErrorAttachment::DirectRootItem(plan.ordinal),
            128,
        )? {
            return Ok(HirItem::Expression(expression));
        }
    }
    match lower_simple_chain(
        parsed,
        &plan.node,
        namespace,
        counters,
        occurrence.clone(),
        scope,
    )? {
        SimpleChainLowering::Resolved {
            expression,
            semantic_error,
        } => {
            if let Some((kind, range)) = semantic_error {
                sink.lowering(
                    kind,
                    HirErrorAttachment::DirectRootItem(plan.ordinal),
                    range,
                )?;
            }
            Ok(HirItem::Expression(expression))
        }
        SimpleChainLowering::Unsupported { range } => {
            causal_errors.push(sink.lowering(
                HirErrorKind::UnsupportedExpression,
                HirErrorAttachment::DirectRootItem(plan.ordinal),
                range.clone(),
            )?);
            Ok(HirItem::Expression(ResolvedExpr::Error {
                occurrence,
                errors: causal_errors.into_boxed_slice(),
                range,
            }))
        }
    }
}

fn lower_body(
    plan: &RootPlan,
    parsed: &ParsedFile,
    namespace: &ModuleNamespace,
    id: &DefId,
    mut causal_errors: Vec<HirErrorId>,
    sink: &mut ErrorSink,
    counters: &mut LoweringCounters,
    occurrence: HirOccurrenceId,
    scope: &ScopeStack,
    _next_occurrence_ordinal: &mut u32,
    _body_depth_budget: usize,
    #[cfg(any(feature = "shadow", test))]
    simple_body_projection: Option<local_source::SimpleBodyProjection>,
) -> Result<(ResolvedExpr, Option<(HirErrorKind, Range<usize>)>), HirAvailabilityError> {
    let Some(body) = plan
        .node
        .children()
        .find(|node| node.kind() == SyntaxKind::BindingBody)
    else {
        causal_errors.push(sink.lowering(
            HirErrorKind::MissingBody,
            HirErrorAttachment::Value(id.clone()),
            plan.range.clone(),
        )?);
        return Ok((
            ResolvedExpr::Error {
                occurrence,
                errors: causal_errors.into_boxed_slice(),
                range: plan.range.clone(),
            },
            None,
        ));
    };
    let children = body.children().collect::<Vec<_>>();
    if matches!(children.as_slice(), [child] if child.kind() == SyntaxKind::IndentedStatementBlock)
    {
        causal_errors.push(sink.lowering(
            HirErrorKind::UnsupportedExpression,
            HirErrorAttachment::Value(id.clone()),
            range_of(&body),
        )?);
        return Ok((
            ResolvedExpr::Error {
                occurrence,
                errors: causal_errors.into_boxed_slice(),
                range: range_of(&body),
            },
            None,
        ));
    }
    if has_recovery(&body) {
        return Ok((
            ResolvedExpr::Error {
                occurrence,
                errors: causal_errors.into_boxed_slice(),
                range: range_of(&body),
            },
            None,
        ));
    }
    let [chain] = children.as_slice() else {
        causal_errors.push(sink.lowering(
            HirErrorKind::UnsupportedExpression,
            HirErrorAttachment::Value(id.clone()),
            range_of(&body),
        )?);
        return Ok((
            ResolvedExpr::Error {
                occurrence,
                errors: causal_errors.into_boxed_slice(),
                range: range_of(&body),
            },
            None,
        ));
    };
    if chain.kind() != SyntaxKind::OperatorChain {
        causal_errors.push(sink.lowering(
            HirErrorKind::UnsupportedExpression,
            HirErrorAttachment::Value(id.clone()),
            range_of(&body),
        )?);
        return Ok((
            ResolvedExpr::Error {
                occurrence,
                errors: causal_errors.into_boxed_slice(),
                range: range_of(&body),
            },
            None,
        ));
    }
    if counters.ordinary_source_carriers {
        let owner_item_index = usize::try_from(plan.ordinal)
            .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        if let Some(expression) = lower_ordinary_admission(
            parsed,
            chain,
            namespace,
            &causal_errors,
            counters,
            occurrence.clone(),
            owner_item_index,
            scope,
        )? {
            return Ok((expression, None));
        }
    }
    #[cfg(any(feature = "shadow", test))]
    if counters.shadow_applications {
        if let Some(expression) = lower_shadow_application(
            parsed,
            chain,
            namespace,
            counters,
            occurrence.clone(),
            scope,
            _next_occurrence_ordinal,
            sink,
            HirErrorAttachment::Value(id.clone()),
            _body_depth_budget,
        )? {
            return Ok((expression, None));
        }
    }
    #[cfg(any(feature = "shadow", test))]
    let lowered = match simple_body_projection {
        Some(local_source::SimpleBodyProjection::Atom(atom)) => {
            lower_leaf(atom, namespace, counters, occurrence.clone(), scope)?
        }
        Some(local_source::SimpleBodyProjection::Unsupported) => {
            SimpleChainLowering::Unsupported {
                range: range_of(chain),
            }
        }
        None => lower_simple_chain(
            parsed,
            chain,
            namespace,
            counters,
            occurrence.clone(),
            scope,
        )?,
    };
    #[cfg(not(any(feature = "shadow", test)))]
    let lowered = lower_simple_chain(
        parsed,
        chain,
        namespace,
        counters,
        occurrence.clone(),
        scope,
    )?;
    match lowered {
        SimpleChainLowering::Resolved {
            expression,
            semantic_error,
        } => Ok((expression, semantic_error)),
        SimpleChainLowering::Unsupported { range } => {
            causal_errors.push(sink.lowering(
                HirErrorKind::UnsupportedExpression,
                HirErrorAttachment::Value(id.clone()),
                range.clone(),
            )?);
            Ok((
                ResolvedExpr::Error {
                    occurrence,
                    errors: causal_errors.into_boxed_slice(),
                    range,
                },
                None,
            ))
        }
    }
}

enum SimpleChainLowering {
    Resolved {
        expression: ResolvedExpr,
        semantic_error: Option<(HirErrorKind, Range<usize>)>,
    },
    Unsupported {
        range: Range<usize>,
    },
}

#[cfg(any(feature = "shadow", test))]
fn lower_shadow_application(
    parsed: &ParsedFile,
    chain: &SyntaxNode,
    namespace: &ModuleNamespace,
    counters: &mut LoweringCounters,
    occurrence: HirOccurrenceId,
    scope: &ScopeStack,
    next_occurrence_ordinal: &mut u32,
    sink: &mut ErrorSink,
    attachment: HirErrorAttachment,
    depth_budget: usize,
) -> Result<Option<ResolvedExpr>, HirAvailabilityError> {
    // Preflight the whole bounded tree before publishing occurrences or errors.
    let Some(plan) = shadow_application_plan(parsed, chain, true)? else {
        return Ok(None);
    };
    if plan.height > depth_budget {
        return Err(HirAvailabilityError::StructuralProjection);
    }
    lower_shadow_application_plan(
        parsed,
        plan,
        namespace,
        counters,
        occurrence,
        scope,
        next_occurrence_ordinal,
        sink,
        attachment,
    )
    .map(Some)
}

#[cfg(any(feature = "shadow", test))]
struct ShadowApplicationPlan {
    height: usize,
    callee: SyntaxNode,
    tail: SyntaxNode,
    argument: SyntaxNode,
    nested: Option<Box<ShadowApplicationPlan>>,
    nested_callee: Option<Box<ShadowApplicationPlan>>,
    grouped: bool,
    range: Range<usize>,
}

#[cfg(any(feature = "shadow", test))]
fn shadow_application_plan(
    parsed: &ParsedFile,
    chain: &SyntaxNode,
    allow_nested: bool,
) -> Result<Option<ShadowApplicationPlan>, HirAvailabilityError> {
    let associated = associate_chain_owned(parsed, chain.clone())
        .map_err(|error| match error {
            AssociationError::ExactOperatorEnvironment => {
                HirAvailabilityError::ExactOperatorEnvironment
            }
            AssociationError::StructuralInvariant => HirAvailabilityError::StructuralProjection,
            AssociationError::Allocation => HirAvailabilityError::IdentityExhausted,
        })?
        .into_hir();
    let HirExpr::Value {
        kind: source_form,
        children: operands,
        range,
    } = associated
    else {
        return Ok(None);
    };
    if !matches!(source_form, SyntaxKind::MlArgument | SyntaxKind::CallTail) {
        return Ok(None);
    }
    let [callee_shape, argument_shape] = operands.as_slice() else {
        return Ok(None);
    };
    let leaf = |shape: &HirExpr| matches!(shape, HirExpr::Value { kind: SyntaxKind::IdentifierExpression | SyntaxKind::IntegerLiteral, children, .. } if children.is_empty());
    let children = chain.children().collect::<Vec<_>>();
    if allow_nested && source_form == SyntaxKind::MlArgument && leaf(argument_shape) {
        if let (
            HirExpr::Value {
                kind: SyntaxKind::MlArgument,
                children: inner,
                range: inner_range,
            },
            [head, first_tail, second_tail],
        ) = (callee_shape, children.as_slice())
        {
            if let [first_callee, first_argument] = inner.as_slice() {
                if leaf(first_callee)
                    && leaf(first_argument)
                    && range_of(head) == *first_callee.range()
                    && first_tail.kind() == SyntaxKind::MlArgument
                    && second_tail.kind() == SyntaxKind::MlArgument
                {
                    let operand_node = |tail: &SyntaxNode, shape: &HirExpr| {
                        let HirExpr::Value { kind, .. } = shape else {
                            return None;
                        };
                        let nodes = tail
                            .descendants()
                            .filter(|node| node.kind() == *kind && range_of(node) == *shape.range())
                            .collect::<Vec<_>>();
                        match nodes.as_slice() {
                            [node] => Some(node.clone()),
                            _ => None,
                        }
                    };
                    if let (Some(first_argument), Some(argument)) = (
                        operand_node(first_tail, first_argument),
                        operand_node(second_tail, argument_shape),
                    ) {
                        return Ok(Some(ShadowApplicationPlan {
                            height: 3,
                            callee: head.clone(),
                            tail: second_tail.clone(),
                            argument,
                            nested: None,
                            grouped: false,
                            range,
                            nested_callee: Some(Box::new(ShadowApplicationPlan {
                                height: 2,
                                callee: head.clone(),
                                tail: first_tail.clone(),
                                argument: first_argument,
                                nested: None,
                                nested_callee: None,
                                grouped: false,
                                range: inner_range.clone(),
                            })),
                        }));
                    }
                }
            }
        }
    }
    if !leaf(callee_shape) {
        return Ok(None);
    }
    let [callee_node, tail] = children.as_slice() else {
        return Ok(None);
    };
    if tail.kind() != source_form || range_of(callee_node) != *callee_shape.range() {
        return Ok(None);
    }
    let grouped = allow_nested
        && source_form == SyntaxKind::MlArgument
        && matches!(argument_shape, HirExpr::Value { kind: SyntaxKind::ParenthesizedExpression, children, .. }
            if matches!(children.as_slice(), [HirExpr::Value { kind: SyntaxKind::MlArgument | SyntaxKind::CallTail, .. }]));
    let argument_kind = if grouped {
        SyntaxKind::ParenthesizedExpression
    } else if leaf(argument_shape) {
        match argument_shape {
            HirExpr::Value { kind, .. } => *kind,
            _ => unreachable!(),
        }
    } else if allow_nested
        && source_form == SyntaxKind::CallTail
        && matches!(
            argument_shape,
            HirExpr::Value {
                kind: SyntaxKind::MlArgument | SyntaxKind::CallTail,
                ..
            }
        )
    {
        SyntaxKind::OperatorChain
    } else {
        return Ok(None);
    };
    let argument_nodes = tail
        .descendants()
        .filter(|node| node.kind() == argument_kind && range_of(node) == *argument_shape.range())
        .collect::<Vec<_>>();
    let [argument_node] = argument_nodes.as_slice() else {
        return Ok(None);
    };
    // Association retains element expressions but omits tuple punctuation.
    // A direct trailing comma still makes a one-tuple, rather than a Group.
    if grouped
        && argument_node.children_with_tokens().any(|element| {
            element
                .into_token()
                .is_some_and(|token| token.kind() == SyntaxKind::Comma)
        })
    {
        return Ok(None);
    }
    let nested = if grouped || argument_kind == SyntaxKind::OperatorChain {
        let nested_chain = if grouped {
            let mut stack = argument_node.children().collect::<Vec<_>>();
            let mut chains = Vec::new();
            while let Some(node) = stack.pop() {
                if node.kind() == SyntaxKind::OperatorChain {
                    chains.push(node);
                } else {
                    stack.extend(node.children());
                }
            }
            let [chain] = chains.as_slice() else {
                return Ok(None);
            };
            chain.clone()
        } else {
            argument_node.clone()
        };
        let Some(plan) = shadow_application_plan(parsed, &nested_chain, false)? else {
            return Ok(None);
        };
        Some(Box::new(plan))
    } else {
        None
    };
    let argument_height = nested.as_ref().map_or(1, |plan| plan.height);
    let height = 1 + argument_height + usize::from(grouped);
    Ok(Some(ShadowApplicationPlan {
        height,
        callee: callee_node.clone(),
        tail: tail.clone(),
        argument: argument_node.clone(),
        nested,
        nested_callee: None,
        grouped,
        range,
    }))
}

#[cfg(any(feature = "shadow", test))]
fn lower_shadow_application_plan(
    parsed: &ParsedFile,
    plan: ShadowApplicationPlan,
    namespace: &ModuleNamespace,
    counters: &mut LoweringCounters,
    occurrence: HirOccurrenceId,
    scope: &ScopeStack,
    next_occurrence_ordinal: &mut u32,
    sink: &mut ErrorSink,
    attachment: HirErrorAttachment,
) -> Result<ResolvedExpr, HirAvailabilityError> {
    let ShadowApplicationPlan {
        height: _,
        callee: callee_node,
        tail,
        argument: argument_node,
        nested,
        nested_callee,
        grouped,
        range,
    } = plan;
    let source_form = tail.kind();
    let Some(key) = counters.source_nodes.get(&tail).cloned() else {
        return Err(HirAvailabilityError::StructuralProjection);
    };
    let mut errors = vec![sink.lowering(
        HirErrorKind::UnsupportedExpression,
        attachment.clone(),
        range.clone(),
    )?];
    let computed_callee = if let Some(plan) = nested_callee {
        let child_occurrence = next_occurrence(&occurrence.artifact, next_occurrence_ordinal)?;
        let callee = lower_shadow_application_plan(
            parsed,
            *plan,
            namespace,
            counters,
            child_occurrence,
            scope,
            next_occurrence_ordinal,
            sink,
            attachment.clone(),
        )?;
        if let ResolvedExpr::Apply {
            errors: nested_errors,
            ..
        } = &callee
        {
            errors.extend(nested_errors.iter().copied());
        }
        Some(callee)
    } else {
        None
    };
    let mut lower_operand = |node: &SyntaxNode| -> Result<ResolvedExpr, HirAvailabilityError> {
        let mut tokens = node
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| matches!(token.kind(), SyntaxKind::Identifier | SyntaxKind::Integer));
        let token = tokens
            .next()
            .ok_or(HirAvailabilityError::StructuralProjection)?;
        if tokens.next().is_some() {
            return Err(HirAvailabilityError::StructuralProjection);
        }
        let child_occurrence = next_occurrence(&occurrence.artifact, next_occurrence_ordinal)?;
        let atom = crate::OwnedAtom {
            source: node.clone(),
            kind: node.kind(),
            spelling: token.text().to_owned(),
            range: crate::range_of_token(&token),
        };
        let SimpleChainLowering::Resolved {
            expression,
            semantic_error,
        } = lower_leaf(atom, namespace, counters, child_occurrence, scope)?
        else {
            return Err(HirAvailabilityError::StructuralProjection);
        };
        if let Some((kind, range)) = semantic_error {
            errors.push(sink.lowering(kind, attachment.clone(), range)?);
        }
        Ok(expression)
    };
    let callee = match computed_callee {
        Some(callee) => callee,
        None => lower_operand(&callee_node)?,
    };
    let argument = if let Some(nested) = nested {
        let child_occurrence = next_occurrence(&occurrence.artifact, next_occurrence_ordinal)?;
        let nested_occurrence = if grouped {
            next_occurrence(&occurrence.artifact, next_occurrence_ordinal)?
        } else {
            child_occurrence.clone()
        };
        let argument = lower_shadow_application_plan(
            parsed,
            *nested,
            namespace,
            counters,
            nested_occurrence,
            scope,
            next_occurrence_ordinal,
            sink,
            attachment,
        )?;
        if let ResolvedExpr::Apply {
            errors: nested_errors,
            ..
        } = &argument
        {
            errors.extend(nested_errors.iter().copied());
        }
        if grouped {
            let key = counters
                .source_nodes
                .get(&argument_node)
                .ok_or(HirAvailabilityError::StructuralProjection)?
                .clone();
            counters
                .source_identity
                .as_mut()
                .expect("shadow route retains source identity")
                .record_occurrence(child_occurrence.clone(), key);
            ResolvedExpr::Group {
                occurrence: child_occurrence,
                inner: Box::new(argument),
                range: range_of(&argument_node),
            }
        } else {
            argument
        }
    } else {
        lower_operand(&argument_node)?
    };
    counters
        .source_identity
        .as_mut()
        .expect("shadow route retains source identity")
        .record_occurrence(occurrence.clone(), key);
    Ok(ResolvedExpr::Apply {
        occurrence,
        source_form,
        callee: Box::new(callee),
        argument: Box::new(argument),
        errors: errors.into_boxed_slice(),
        range,
    })
}

fn lower_simple_chain(
    parsed: &ParsedFile,
    chain: &SyntaxNode,
    namespace: &ModuleNamespace,
    counters: &mut LoweringCounters,
    occurrence: HirOccurrenceId,
    scope: &ScopeStack,
) -> Result<SimpleChainLowering, HirAvailabilityError> {
    let chain_range = range_of(chain);
    let (expression, atom) = associate_chain_owned(parsed, chain.clone())
        .map_err(|error| match error {
            AssociationError::ExactOperatorEnvironment => {
                HirAvailabilityError::ExactOperatorEnvironment
            }
            AssociationError::StructuralInvariant => HirAvailabilityError::StructuralProjection,
            AssociationError::Allocation => HirAvailabilityError::IdentityExhausted,
        })?
        .into_parts();
    let Some(atom) = atom else {
        return Ok(SimpleChainLowering::Unsupported { range: chain_range });
    };
    if !matches!(expression, HirExpr::Value { children, .. } if children.is_empty()) {
        return Ok(SimpleChainLowering::Unsupported { range: chain_range });
    }
    lower_leaf(atom, namespace, counters, occurrence, scope)
}

fn lower_leaf(
    atom: crate::OwnedAtom,
    namespace: &ModuleNamespace,
    counters: &mut LoweringCounters,
    occurrence: HirOccurrenceId,
    scope: &ScopeStack,
) -> Result<SimpleChainLowering, HirAvailabilityError> {
    lower_leaf_with_identity(atom, namespace, counters, occurrence, scope, true)
}

fn lower_leaf_with_identity(
    atom: crate::OwnedAtom,
    namespace: &ModuleNamespace,
    counters: &mut LoweringCounters,
    occurrence: HirOccurrenceId,
    scope: &ScopeStack,
    record_identity: bool,
) -> Result<SimpleChainLowering, HirAvailabilityError> {
    if record_identity {
        if let Some(source) = &mut counters.source_identity {
        if let Some(key) = counters.source_nodes.get(&atom.source) {
            source.record_occurrence(occurrence.clone(), key.clone());
        }
        }
    }
    match atom.kind {
        SyntaxKind::IntegerLiteral => Ok(SimpleChainLowering::Resolved {
            expression: ResolvedExpr::Integer {
                occurrence,
                spelling: {
                    counters.copied_spelling_bytes += atom.spelling.len();
                    atom.spelling
                },
                range: atom.range,
            },
            semantic_error: None,
        }),
        SyntaxKind::IdentifierExpression => {
            counters.copied_spelling_bytes += atom.spelling.len();
            let name = HirName {
                spelling: atom.spelling,
                range: atom.range.clone(),
            };
            let (resolution, kind) = if let Some(parameter) = scope.parameter(&name.spelling) {
                (NameResolution::Parameter(parameter.id.clone()), None)
            } else {
                match namespace.get(&name.spelling) {
                    Some(ModuleNameResolution::Local(definition)) => {
                        (NameResolution::Resolved(definition.clone()), None)
                    }
                    Some(ModuleNameResolution::Imported(identity)) => {
                        (NameResolution::Imported(identity.clone()), None)
                    }
                    #[cfg(any(feature = "shadow", test))]
                    Some(ModuleNameResolution::ImportedOperation(_)) => (
                        NameResolution::Unresolved,
                        Some(HirErrorKind::UnresolvedName),
                    ),
                    Some(ModuleNameResolution::Ambiguous) => (NameResolution::Ambiguous, Some(HirErrorKind::AmbiguousName)),
                    None => (
                        NameResolution::Unresolved,
                        Some(HirErrorKind::UnresolvedName),
                    ),
                }
            };
            Ok(SimpleChainLowering::Resolved {
                expression: ResolvedExpr::Name {
                    occurrence,
                    range: name.range.clone(),
                    name: name.clone(),
                    resolution,
                },
                semantic_error: kind.map(|kind| (kind, name.range)),
            })
        }
        _ => Err(HirAvailabilityError::StructuralProjection),
    }
}

fn plain_binding_header(
    node: &SyntaxNode,
    _counters: &LoweringCounters,
) -> Option<(HirVisibility, HirName, Vec<AdmittedParameter>)> {
    let header = node
        .children()
        .find(|child| child.kind() == SyntaxKind::BindingHeader)?;
    let visibility = header.children_with_tokens().find_map(|element| {
        let token = element.into_token()?;
        match token.kind() {
            SyntaxKind::MyKw => Some(HirVisibility::Private),
            SyntaxKind::OurKw => Some(HirVisibility::Our),
            SyntaxKind::PubKw => Some(HirVisibility::Public),
            _ => None,
        }
    })?;
    let patterns = header.children().collect::<Vec<_>>();
    let [target] = patterns.as_slice() else {
        return None;
    };
    if target.kind() != SyntaxKind::Pattern || has_recovery(target) {
        return None;
    }
    let target_children = target.children().collect::<Vec<_>>();
    let has_parenthesized_formal = target_children
        .iter()
        .any(|child| child.kind() == SyntaxKind::PatternCallTail);
    let pattern_children = target_children
        .into_iter()
        .filter(|child| {
            !((_counters.local_source
                || (_counters.ordinary_source_carriers && has_parenthesized_formal))
                && child.kind() == SyntaxKind::PatternTypeAnnotation)
        })
        .collect::<Vec<_>>();
    let (head, tails) = pattern_children.split_first()?;
    let head = identifier_pattern_name(head)?;
    let multiple_parameters = _counters.shadow_applications || _counters.local_source;
    if tails.len() > 1 && !multiple_parameters {
        return None;
    }
    let mut parameters = Vec::with_capacity(tails.len());
    for tail in tails {
        if (_counters.local_source || _counters.ordinary_source_carriers)
            && tail.kind() == SyntaxKind::PatternCallTail
        {
            if has_recovery(tail) {
                return None;
            }
            let arguments = tail.children().collect::<Vec<_>>();
            if arguments.is_empty() {
                parameters.push(unit_pattern_parameter(tail, _counters)?);
                continue;
            }
            for argument in arguments {
                if argument.kind() != SyntaxKind::Pattern || has_recovery(&argument) {
                    return None;
                }
                let children = argument.children().collect::<Vec<_>>();
                let (identifier, annotation) = match children.as_slice() {
                    [identifier] => (identifier, None),
                    [identifier, annotation]
                        if annotation.kind() == SyntaxKind::PatternTypeAnnotation =>
                    {
                        (identifier, Some(annotation.clone()))
                    }
                    _ => return None,
                };
                parameters.push(AdmittedParameter {
                    name: identifier_pattern_name(identifier)?,
                    source: _counters.source_nodes.get(identifier).cloned(),
                    annotation,
                    unit_pattern: false,
                });
            }
            continue;
        }
        if tail.kind() != SyntaxKind::PatternMlApplicationTail || has_recovery(tail) {
            return None;
        }
        let arguments = tail.children().collect::<Vec<_>>();
        let [argument] = arguments.as_slice() else {
            return None;
        };
        if argument.kind() != SyntaxKind::Pattern || has_recovery(argument) {
            return None;
        }
        let argument_children = argument.children().collect::<Vec<_>>();
        let [argument] = argument_children.as_slice() else {
            return None;
        };
        if _counters.local_source && argument.kind() == SyntaxKind::ParenthesizedPattern
            && argument.children().next().is_none()
        {
            parameters.push(unit_pattern_parameter(argument, _counters)?);
            continue;
        }
        let (argument, annotation) =
            if _counters.local_source && argument.kind() == SyntaxKind::ParenthesizedPattern {
                if argument
                    .children_with_tokens()
                    .filter_map(|element| element.into_token())
                    .any(|token| {
                        !matches!(
                            token.kind(),
                            SyntaxKind::LParen
                                | SyntaxKind::RParen
                                | SyntaxKind::Whitespace
                                | SyntaxKind::Newline
                                | SyntaxKind::LineComment
                                | SyntaxKind::BlockComment
                        )
                    })
                {
                    return None;
                }
                let children = argument.children().collect::<Vec<_>>();
                let [pattern] = children.as_slice() else {
                    return None;
                };
                if pattern.kind() != SyntaxKind::Pattern {
                    return None;
                }
                let children = pattern.children().collect::<Vec<_>>();
                let [identifier, annotation] = children.as_slice() else {
                    return None;
                };
                if annotation.kind() != SyntaxKind::PatternTypeAnnotation {
                    return None;
                }
                (identifier.clone(), Some(annotation.clone()))
            } else {
                ((*argument).clone(), None)
            };
        parameters.push(AdmittedParameter {
            name: identifier_pattern_name(&argument)?,
            source: _counters.source_nodes.get(&argument).cloned(),
            annotation,
            unit_pattern: false,
        });
    }
    Some((visibility, head, parameters))
}

fn unit_pattern_parameter(node: &SyntaxNode, counters: &LoweringCounters) -> Option<AdmittedParameter> {
    let tokens = node.children_with_tokens().filter(|element| !matches!(element.kind(),
        SyntaxKind::Whitespace | SyntaxKind::Newline | SyntaxKind::LineComment | SyntaxKind::BlockComment))
        .map(|element| element.kind()).collect::<Vec<_>>();
    if tokens != [SyntaxKind::LParen, SyntaxKind::RParen] { return None; }
    let range = node.text_range();
    Some(AdmittedParameter {
        // This anonymous slot has no lexical name. Its actual pattern key and
        // discriminator, rather than this display spelling, own its meaning.
        name: HirName { spelling: String::new(), range: usize::from(range.start())..usize::from(range.end()) },
        source: Some(counters.source_nodes.get(node)?.clone()),
        annotation: None,
        unit_pattern: true,
    })
}

fn identifier_pattern_name(pattern: &SyntaxNode) -> Option<HirName> {
    if pattern.kind() != SyntaxKind::IdentifierPattern || has_recovery(pattern) {
        return None;
    }
    let tokens = pattern
        .children_with_tokens()
        .filter_map(|element| element.into_token())
        .collect::<Vec<_>>();
    let [token] = tokens.as_slice() else {
        return None;
    };
    (token.kind() == SyntaxKind::Identifier).then(|| HirName {
        spelling: token.text().to_owned(),
        range: token_range(token),
    })
}

fn has_recovery(node: &SyntaxNode) -> bool {
    node.descendants_with_tokens().any(|element| {
        element
            .as_node()
            .is_some_and(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Invalid))
            || element
                .into_token()
                .is_some_and(|token| token.kind() == SyntaxKind::Error)
    })
}

fn token_range(token: &yu_syntax::SyntaxToken) -> Range<usize> {
    let range = token.text_range();
    u32::from(range.start()) as usize..u32::from(range.end()) as usize
}

fn validated_recoveries(
    parsed: &ParsedFile,
) -> Result<Vec<StructuralRecovery>, HirAvailabilityError> {
    let recoveries = parsed
        .try_structural_recoveries()
        .map_err(|_| HirAvailabilityError::StructuralProjection)?;
    for (index, recovery) in recoveries.iter().enumerate() {
        if recovery.ordinal()
            != u32::try_from(index).map_err(|_| HirAvailabilityError::StructuralProjection)?
        {
            return Err(HirAvailabilityError::StructuralProjection);
        }
    }
    Ok(recoveries)
}

#[derive(Default)]
struct ErrorSink {
    errors: Vec<HirError>,
    diagnostics: Vec<HirDiagnostic>,
}

impl ErrorSink {
    fn syntax(
        &mut self,
        recovery: &StructuralRecovery,
        attachment: HirErrorAttachment,
    ) -> Result<HirErrorId, HirAvailabilityError> {
        let kind = match recovery.kind() {
            StructuralRecoveryKind::Missing => HirErrorKind::InheritedMissing,
            StructuralRecoveryKind::RawError => HirErrorKind::InheritedRawError,
            StructuralRecoveryKind::Invalid => HirErrorKind::InheritedInvalid,
        };
        self.push(
            HirErrorOrigin::Syntax,
            attachment,
            recovery.range().clone(),
            kind,
            false,
        )
    }

    fn lowering(
        &mut self,
        kind: HirErrorKind,
        attachment: HirErrorAttachment,
        range: Range<usize>,
    ) -> Result<HirErrorId, HirAvailabilityError> {
        self.push(HirErrorOrigin::Lowering, attachment, range, kind, true)
    }

    fn push(
        &mut self,
        origin: HirErrorOrigin,
        attachment: HirErrorAttachment,
        range: Range<usize>,
        kind: HirErrorKind,
        diagnostic: bool,
    ) -> Result<HirErrorId, HirAvailabilityError> {
        self.errors.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        if diagnostic {
            self.diagnostics.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        }
        let error = HirErrorId(
            u32::try_from(self.errors.len())
                .map_err(|_| HirAvailabilityError::IdentityExhausted)?,
        );
        let diagnostic = if diagnostic {
            let id = HirDiagnosticId(
                u32::try_from(self.diagnostics.len())
                    .map_err(|_| HirAvailabilityError::IdentityExhausted)?,
            );
            self.diagnostics.push(HirDiagnostic {
                id,
                error,
                kind,
                range: range.clone(),
            });
            Some(id)
        } else {
            None
        };
        self.errors.push(HirError {
            id: error,
            origin,
            attachment,
            range,
            kind,
            diagnostic,
        });
        Ok(error)
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

    fn parsed(source: &str) -> ParsedFile {
        let source: Arc<SourceText> = Arc::from(source);
        let header = Arc::new(scan_header(source.clone()));
        parse_file(source, header, Arc::new(SyntaxEnvironment::empty()))
    }

    fn identity() -> ModuleIdentity {
        ModuleIdentity::source_root(FileId::new(FileKey::new("test", "counters.yu")))
    }

    fn indexed(path: &str, source: &str) -> source_exports::SourceExportIndex {
        let parsed = parsed(source);
        let identity = ModuleIdentity::source_root(FileId::new(FileKey::new("test", path)));
        index_source_exports(identity, &parsed).unwrap()
    }

    #[test]
    fn source_imports_resolve_named_alias_and_glob_by_exact_provider() {
        let indexes = vec![
            indexed("lib/std.yu", "pub mod core;\npub mod prelude;"),
            indexed("lib/std/core.yu", "pub id x = x"),
            indexed("lib/std/prelude.yu", "pub use std::core::*"),
        ];
        let consumer = parsed("use std::core::id as identity\npub first = identity 1\npub second = id 2");
        let identity = ModuleIdentity::source_root(FileId::new(FileKey::new("test", "consumer.yu")));
        let imports = SemanticImports::with_source_imports(&consumer, &identity, &indexes).unwrap();
        let environment = imports.source_imports.as_ref().unwrap();
        let source_exports::SourceImportBinding::Resolved(binding) = environment.resolve("identity").unwrap() else {
            panic!("named alias resolves to one exact source provider");
        };
        assert_eq!(binding.module.as_ref(), "std::core");
        assert_eq!(binding.name.as_ref(), "id");
        let source_exports::SourceImportBinding::Resolved(prelude_binding) = environment.resolve("id").unwrap() else {
            panic!("implicit prelude glob resolves to the same provider");
        };
        assert_eq!(prelude_binding.identity(), binding.identity());
    }

    #[test]
    fn explicit_import_items_require_the_complete_parse_bound_resolver() {
        let indexes = vec![
            indexed("lib/std.yu", "pub mod core;\npub mod prelude;"),
            indexed("lib/std/core.yu", "pub id x = x"),
            indexed("lib/std/prelude.yu", "pub use std::core::*"),
        ];
        let text = "use std::core::id as identity\nmy main = identity 7";
        let consumer = parsed(text);
        let identity = identity();
        let complete = SemanticImports::with_source_imports(&consumer, &identity, &indexes).unwrap();
        let hir = lower_module(identity.clone(), &consumer, complete).unwrap();
        assert!(matches!(&hir.items()[0], HirItem::Import { range } if text[range.clone()].trim() == "use std::core::id as identity"));
        assert!(!hir.errors().iter().any(|error| error.kind() == HirErrorKind::UnsupportedItem));
        let implicit = SemanticImports::with_implicit_prelude(&consumer, &identity, &indexes).unwrap();
        let unverified = lower_module(identity.clone(), &consumer, implicit).unwrap();
        assert!(matches!(&unverified.items()[0], HirItem::Error { .. }));
        let syntax = source_exports::SourceImportEnvironment::for_syntax_operators(&consumer, &identity, &indexes).unwrap();
        assert!(!syntax.complete_source_uses);
        let selected = std::collections::HashSet::from([consumer.source_root().children().nth(1).unwrap().key()]);
        let partial = SemanticImports::with_selected_source_imports(&consumer, &identity, &indexes, &selected).unwrap();
        assert!(!partial.source_imports().unwrap().complete_source_uses);
        let other = parsed(text);
        let foreign = SemanticImports::with_source_imports(&consumer, &identity, &indexes).unwrap();
        assert!(matches!(lower_module(identity, &other, foreign), Err(HirAvailabilityError::ForeignSourceImport)));
    }

    #[test]
    fn empty_glob_imports_still_validate_module_existence_and_visibility() {
        let indexes = vec![
            indexed("lib/std.yu", "pub mod empty;\nmod hidden;\npub mod prelude;"),
            indexed("lib/std/empty.yu", ""),
            indexed("lib/std/hidden.yu", ""),
            indexed("lib/std/prelude.yu", ""),
        ];
        for path in ["std::missing", "std::hidden"] {
            let consumer = parsed(&format!("use {path}::*\nmy main = 7"));
            assert!(matches!(SemanticImports::with_source_imports(&consumer, &identity(), &indexes), Err(HirAvailabilityError::SourceImportResolutionUnavailable)), "{path}");
        }
        let consumer = parsed("use std::empty::*\nmy main = 7");
        let imports = SemanticImports::with_source_imports(&consumer, &identity(), &indexes).unwrap();
        let hir = lower_module(identity(), &consumer, imports).unwrap();
        assert!(matches!(hir.items()[0], HirItem::Import { .. }));
    }

    #[test]
    fn selected_local_source_lowers_only_parse_owned_direct_roots() {
        let parsed = parsed("pub wanted = 1\npub unused = missing.field");
        let roots = parsed.source_root().children().collect::<Vec<_>>();
        let selected = [roots[0].key()].into_iter().collect();
        let hir = lower_module_with_selected_local_source(
            identity(), &parsed, SemanticImports::empty(), selected,
        ).unwrap();
        assert_eq!(hir.items().len(), 1);
        assert_eq!(hir.local_sources.len(), 1);
        assert_eq!(hir.source_identity.as_ref().unwrap().definitions.len(), 1);

        let nested = roots[0].children().next().unwrap().key();
        assert_eq!(
            lower_module_with_selected_local_source(
                identity(), &parsed, SemanticImports::empty(), [nested].into_iter().collect(),
            ),
            Err(HirAvailabilityError::StructuralProjection),
        );
    }

    #[test]
    fn selected_source_imports_skip_unused_import_leaves() {
        let indexes = vec![
            indexed("lib/std.yu", "pub mod core;\npub mod prelude;"),
            indexed("lib/std/core.yu", "pub id x = x"),
            indexed("lib/std/prelude.yu", ""),
        ];
        let parsed = parsed("use std::core::missing\npub selected = 1");
        let identity = ModuleIdentity::source_root(FileId::new(FileKey::new("test", "selected.yu")));
        let roots = parsed.source_root().children().collect::<Vec<_>>();
        let selected = [roots[1].key()].into_iter().collect::<std::collections::HashSet<_>>();

        assert_eq!(
            SemanticImports::with_source_imports(&parsed, &identity, &indexes).unwrap_err(),
            HirAvailabilityError::SourceImportResolutionUnavailable,
        );
        let imports = SemanticImports::with_selected_source_imports(&parsed, &identity, &indexes, &selected).unwrap();
        let hir = lower_module_with_selected_local_source(identity, &parsed, imports, selected).unwrap();
        assert_eq!(hir.items().len(), 1);
        assert!(hir.errors().is_empty());
    }

    #[test]
    fn local_source_admits_parenthesized_multiple_annotated_formals() {
        let parsed = parsed("pub combine(left: int, right: str): int = left");
        assert!(parsed.syntax_diagnostics().unwrap().is_empty());
        let hir = lower_module_with_local_source(identity(), &parsed, SemanticImports::empty()).unwrap();
        let HirItem::Binding(binding) = &hir.items()[0] else { panic!("function header remains a binding") };
        assert_eq!(binding.parameters().len(), 2);
        assert_eq!(binding.parameters()[0].name().spelling(), "left");
        assert_eq!(binding.parameters()[1].name().spelling(), "right");
        assert!(hir.local_source(binding.definition_root()).unwrap().is_some());
    }

    #[test]
    fn operator_rhs_uses_its_existing_expression_source_carrier() {
        let parsed_file = parsed(r"pub infix (+) 5.0.0 5.0.1 = \x -> \y -> x.add y");
        assert!(parsed_file.syntax_diagnostics().unwrap().is_empty());
        let module = identity();
        let hir = lower_module_with_local_source(module.clone(), &parsed_file, SemanticImports::empty()).unwrap();
        assert!(hir.items().iter().all(|item| !matches!(item, HirItem::Binding(_))));
        assert!(hir.source_member_carrier_outcomes().is_empty());
        let provider_index = index_source_exports(module.clone(), &parsed_file).unwrap();
        let operator = &parsed_file.header().operators()[0];
        let operator_owner = provider_index.operator_owner_for_receipt(
            module.module(), parsed_file.revision(), operator.range(), "+", yu_syntax::OperatorFixity::Infix,
        ).unwrap();
        let expression = hir.items().iter().find_map(|item| match item {
            HirItem::Expression(expression) => Some(expression),
            _ => None,
        }).expect("the operator RHS is retained as its ordinary expression item");
        let root = hir.expression_root(expression.occurrence()).unwrap().unwrap();
        let owner = SourceRootId::Expression(root.clone());
        assert_eq!(hir.expression_source_key(root).unwrap(), Some(operator_owner.body()));
        assert!(parsed_file.owns_source_key(operator_owner.declaration()));
        assert!(parsed_file.owns_source_key(operator_owner.body()));
        assert_eq!(hir.source_operator_root_for(&operator_owner, &provider_index).unwrap(), Some(owner.clone()));
        let source = hir.local_source_for(&owner).unwrap().expect("operator RHS has a source carrier");
        let body = source.expression(source.body()).unwrap();
        assert_eq!(body.range, operator_owner.body_range().clone());
        assert_eq!(parsed_file.source().get(body.range.clone()), Some(r"\x -> \y -> x.add y"));
        assert!(source.expressions().iter().any(|expression| matches!(
            expression.form,
            local_source::LocalSourceForm::Lambda { .. }
        )));
        assert!(matches!(hir.source_carrier_for(&owner).unwrap(), Some(local_source::SourceCarrierOutcome::Supported(_))));
        let foreign_parsed = parsed(r"pub infix (+) 5.0.0 5.0.1 = \x -> \y -> x.add y");
        let foreign_hir = lower_module_with_local_source(
            module, &foreign_parsed, SemanticImports::empty(),
        ).unwrap();
        assert!(foreign_hir.source_operator_root_for(&operator_owner, &provider_index).unwrap().is_none(),
            "identical bytes in a separate parse cannot reuse provider source keys");
    }

    #[test]
    fn local_source_admits_multi_formal_where_clause_and_field_tail() {
        for source in [
            "pub display(spec: int, value: str): int = spec",
            "pub display(spec: int, value: str): int = value",
            "pub display(spec: int, value: 'a): int =\n    where 'a: Display\n    value",
            "pub display(spec: int, value: 'a): int =\n    where 'a: Display\n    value.show",
        ] {
            let parsed = parsed(source);
            assert!(parsed.syntax_diagnostics().unwrap().is_empty(), "{source}");
            let result = lower_module_with_local_source(identity(), &parsed, SemanticImports::empty());
            assert!(result.is_ok(), "{source}: {:?}", result.err());
            let hir = result.unwrap();
            let HirItem::Binding(binding) = &hir.items()[0] else { panic!("function header remains a binding") };
            assert_eq!(binding.parameters().len(), 2);
            assert!(hir.local_source(binding.definition_root()).unwrap().is_some());
        }
    }

    #[test]
    fn pinned_builtin_namespace_forms_distinct_primitive_values() {
        let parsed = parsed("pub add: int -> int -> int = builtin_op::int_add\npub sub = builtin_op::int_sub\npub mul = builtin_op::int_mul\npub divide = builtin_op::int_div");
        assert!(parsed.syntax_diagnostics().unwrap().is_empty());
        let hir = lower_module_with_local_source(identity(), &parsed, SemanticImports::empty()).unwrap();
        let sources = hir.items().iter().filter_map(|item| match item {
            HirItem::Binding(binding) => hir.local_source(binding.definition_root()).unwrap(),
            _ => None,
        }).collect::<Vec<_>>();
        assert!(sources.iter().flat_map(|source| source.expressions()).any(|expression| matches!(
            expression.form,
            local_source::LocalSourceForm::Primitive {
                operation: source_annotation::PinnedPrimitiveOp::IntAdd,
            }
        )));
        for expected in [source_annotation::PinnedPrimitiveOp::IntSub, source_annotation::PinnedPrimitiveOp::IntMul] {
            assert!(sources.iter().flat_map(|source| source.expressions()).any(|expression| matches!(
                &expression.form, local_source::LocalSourceForm::Primitive { operation } if operation == &expected)));
        }
        assert!(sources.iter().flat_map(|source| source.expressions()).any(|expression| matches!(
            &expression.form,
            local_source::LocalSourceForm::Primitive {
                operation: source_annotation::PinnedPrimitiveOp::Unsupported(name),
            } if name.as_ref() == "int_div"
        )));
        assert!(!sources.iter().flat_map(|source| source.expressions()).any(|expression| matches!(
            expression.form,
            local_source::LocalSourceForm::Operation {
                resolution: source_annotation::SourceOperationResolution::Resolved(_),
            }
        )));
    }

    #[test]
    fn ordinary_effect_operations_keep_source_declaration_identity() {
        let parsed = parsed("act custom:\n    our ping: int -> int\npub run = custom::ping 1");
        assert!(parsed.syntax_diagnostics().unwrap().is_empty());
        let hir = lower_module_with_local_source(identity(), &parsed, SemanticImports::empty()).unwrap();
        let HirItem::Binding(binding) = hir.items().iter().find(|item| matches!(item, HirItem::Binding(binding) if binding.name().spelling() == "run")).unwrap() else { unreachable!() };
        let source = hir.local_source(binding.definition_root()).unwrap().unwrap();
        let operation = source.expressions().iter().find(|expression| matches!(expression.form, local_source::LocalSourceForm::Operation { .. })).unwrap();
        assert!(matches!(
            &operation.form,
            local_source::LocalSourceForm::Operation {
                resolution: source_annotation::SourceOperationResolution::Resolved(declaration),
            } if declaration.spelling.as_ref() == "ping"
        ));
        assert!(!source.expressions().iter().any(|expression| matches!(expression.form, local_source::LocalSourceForm::Primitive { .. })));
    }

    #[test]
    fn admission_root_collision_is_rejected_without_overwriting_or_publishing() {
        let parsed = parsed("my first = 1; my second = 2");
        let roots: Vec<_> = parsed.source_root().children().collect();
        let original_key = roots[0].key();
        let conflicting_key = roots[1].key();
        let artifact = mint_artifact_token();
        let mut ordinal = 0;
        let root = next_occurrence(&artifact, &mut ordinal).unwrap();
        let mut source = crate::source_identity::HirSourceIdentity::new(&parsed);
        source.record_occurrence(root.clone(), original_key.clone());

        assert_eq!(
            validate_admission_root_mapping(&source, &root, &conflicting_key),
            Err(HirAvailabilityError::InconsistentIdentity),
        );
        assert_eq!(source.occurrences.get(&root), Some(&original_key));

        let mut stage = source.empty_stage();
        stage.record_unique_occurrence(root.clone(), conflicting_key);
        assert_eq!(
            source.append_stage(stage),
            Err(HirAvailabilityError::StructuralProjection),
        );
        assert_eq!(source.occurrences.get(&root), Some(&original_key));
    }

    #[test]
    fn recovery_partition_visits_and_emits_each_occurrence_once() {
        let parsed = parsed("my x = @; my y = (");
        let recoveries = parsed.structural_recoveries();
        let mut counters = LoweringCounters::default();
        let module = lower_module_with_counters(
            identity(),
            &parsed,
            SemanticImports::empty(),
            &mut counters,
        )
        .expect("recovery lowering remains available");

        assert_eq!(counters.recovery_visits, recoveries.len());
        assert_eq!(counters.syntax_emissions, recoveries.len());
        assert_eq!(
            module
                .errors()
                .iter()
                .filter(|error| error.origin() == HirErrorOrigin::Syntax)
                .count(),
            recoveries.len()
        );
        assert_eq!(counters.copied_spelling_bytes, b"xy".len());
    }

    #[test]
    fn occurrence_ids_remain_distinct_for_equal_zero_width_error_ranges() {
        let artifact = mint_artifact_token();
        let first = ResolvedExpr::Error {
            occurrence: HirOccurrenceId::new(artifact.clone(), 0),
            errors: Box::new([]),
            range: 0..0,
        };
        let second = ResolvedExpr::Error {
            occurrence: HirOccurrenceId::new(artifact, 1),
            errors: Box::new([]),
            range: 0..0,
        };
        assert_eq!(first.range(), second.range());
        assert_ne!(first.occurrence(), second.occurrence());
    }

    #[test]
    fn parameter_id_has_the_exact_positive_trait_surface() {
        fn assert_traits<T: Clone + std::fmt::Debug + Eq + Hash>() {}
        assert_traits::<HirParameterId>();
    }

    #[test]
    fn parameter_has_the_exact_positive_trait_surface() {
        fn assert_traits<T: Clone + std::fmt::Debug + Eq>() {}
        assert_traits::<HirParameter>();
    }

    #[test]
    fn evaluation_classification_is_private_and_frozen_on_bindings() {
        let module = lower_module(
            identity(),
            &parsed("my x = 1; my y = x; my f p = p; my missing = nope; my bad = @; my app = f 1; my group = (1); my lambda_app p = p 1; my lambda_plain p = p"),
            SemanticImports::empty(),
        )
        .expect("lowering remains available");
        let bindings: Vec<_> = module.items().iter().filter_map(|item| match item { HirItem::Binding(binding) => Some(binding), _ => None }).collect();
        assert_eq!(bindings.len(), 9);
        let [x, y, f, missing, bad, app, group, lambda_app, lambda_plain] = bindings.as_slice() else { panic!("nine bindings") };
        assert_eq!(x.evaluation_class, Some(EvaluationClass::FetchValue));
        assert_eq!(y.evaluation_class, Some(EvaluationClass::FetchValue));
        assert_eq!(f.evaluation_class, Some(EvaluationClass::FetchValue));
        assert_eq!(missing.evaluation_class, None);
        assert_eq!(bad.evaluation_class, None);
        assert_eq!(app.evaluation_class, None);
        assert_eq!(group.evaluation_class, None);
        assert_eq!(lambda_app.evaluation_class, None);
        assert_eq!(lambda_plain.evaluation_class, Some(EvaluationClass::FetchValue));
    }

    #[test]
    fn many_simple_admissions_finalize_at_their_exact_item_indices() {
        let count = 64usize;
        let source = (0..count).map(|index| format!("my v{index} = {index}")).collect::<Vec<_>>().join("; ");
        let parsed = parsed(&source);
        let mut counters = LoweringCounters::default();
        counters.source_identity = Some(crate::source_identity::HirSourceIdentity::new(&parsed));
        counters.source_nodes = crate::source_identity::try_source_keys(&parsed).unwrap();
        counters.ordinary_source_carriers = true;
        let module = lower_module_with_counters(identity(), &parsed, SemanticImports::empty(), &mut counters).unwrap();
        assert_eq!(module.items().len(), count);
        assert_eq!(counters.ordinary_admission_item_visits, count,
            "one indexed owning-item access per admitted body, independent of module length");
    }

    #[test]
    fn def_id_hash_eq_payload_bytes_include_spelling_and_source_root_file_key_text() {
        let realm = "identity-realm";
        let path = "nested/identity-module.yu";
        let module = lower_module(
            ModuleIdentity::source_root(FileId::new(FileKey::new(realm, path))),
            &parsed("my definition = 42"),
            SemanticImports::empty(),
        )
        .expect("simple binding lowers");
        let HirItem::Binding(binding) = &module.items()[0] else {
            panic!("binding");
        };
        assert_eq!(
            binding.id().hash_eq_payload_bytes(),
            realm.len() + path.len() + binding.id().spelling().len()
        );
    }
}

#[cfg(any(feature = "shadow", test))]
pub(crate) fn retain_shadow_local_binding(
    mut hir: HirModule,
    artifact: &crate::shadow::ShadowArtifact,
) -> Result<HirModule, HirAvailabilityError> {
    use crate::shadow::Form;
    let invalid = || HirAvailabilityError::StructuralProjection;
    let (root, _) = hir.captured_source.as_ref().ok_or_else(invalid)?;
    let binding = hir
        .items
        .iter()
        .find_map(|item| match item {
            HirItem::Binding(binding) if binding.definition_root() == root => Some(binding),
            _ => None,
        })
        .ok_or_else(invalid)?;
    let declaration = artifact
        .definition_source_position(&hir, root)
        .map_err(|_| invalid())?;
    let skeleton = artifact
        .declaration_skeleton(&declaration)
        .map_err(|_| invalid())?;
    let input = skeleton.captured_call_input().ok_or_else(invalid)?;
    let ResolvedExpr::Lambda {
        parameter: outer,
        body: old_body,
        ..
    } = &binding.value
    else {
        return Err(invalid());
    };
    let errors = match old_body.as_ref() {
        ResolvedExpr::Error { errors, .. } => errors.clone(),
        _ => return Err(invalid()),
    };
    let local = HirLocalId {
        owner: SourceRootId::Definition(binding.definition_root.clone()),
        ordinal: u32::try_from(0usize).map_err(|_| invalid())?,
    };
    let x = HirParameterId::new(
        binding.definition_root.clone(),
        u32::try_from(binding.parameters.len()).map_err(|_| invalid())?,
    );
    let root = skeleton
        .expression(skeleton.body())
        .map_err(|_| invalid())?;
    let Form::Lambda { body: bind_id, .. } = root.form() else {
        return Err(invalid());
    };
    let bound = skeleton.expression(bind_id).map_err(|_| invalid())?;
    let Form::Bind {
        value,
        body: returned,
        ..
    } = bound.form()
    else {
        return Err(invalid());
    };
    let lambda = skeleton.expression(value).map_err(|_| invalid())?;
    let Form::Lambda {
        parameter,
        body: call_id,
        ..
    } = lambda.form()
    else {
        return Err(invalid());
    };
    let call = skeleton.expression(call_id).map_err(|_| invalid())?;
    let Form::Apply {
        source_form,
        callee,
        argument,
    } = call.form()
    else {
        return Err(invalid());
    };
    let mut pending = Vec::new();
    for item in &hir.items {
        match item {
            HirItem::Binding(binding) => pending.push(&binding.value),
            HirItem::Expression(expression) => pending.push(expression),
            HirItem::Import { .. } | HirItem::Error { .. } => {}
        }
    }
    let mut maximum = None;
    while let Some(expression) = pending.pop() {
        maximum = Some(
            maximum.map_or(expression.occurrence().ordinal(), |current: u32| {
                current.max(expression.occurrence().ordinal())
            }),
        );
        match expression {
            ResolvedExpr::Apply {
                callee, argument, ..
            } => {
                pending.push(argument);
                pending.push(callee);
            }
            ResolvedExpr::Lambda { body, .. } => pending.push(body),
            ResolvedExpr::Group { inner, .. } => pending.push(inner),
            ResolvedExpr::Integer { .. }
            | ResolvedExpr::Name { .. }
            | ResolvedExpr::Error { .. } => {}
        }
    }
    let retained_maximum = hir
        .source_identity
        .as_ref()
        .and_then(|source| source.maximum_occurrence_ordinal());
    let mut next = maximum
        .into_iter()
        .chain(retained_maximum)
        .max()
        .ok_or_else(invalid)?
        .checked_add(1)
        .ok_or_else(invalid)?;
    // Identity minting stays in HIR. Each exact-position crosswalk is checked
    // before the candidate tree can escape this cold opt-in constructor.
    let mut source = hir.source_identity.clone().ok_or_else(invalid)?;
    let mut occurrence =
        |expression: &crate::shadow::Expression| -> Result<HirOccurrenceId, HirAvailabilityError> {
            let id = HirOccurrenceId::new(hir.artifact.clone(), next);
            next = next.checked_add(1).ok_or_else(invalid)?;
            if !source.record_unique_occurrence(
                id.clone(),
                artifact
                    .exact_source_key(expression.position())
                    .map_err(|_| invalid())?,
            ) {
                return Err(invalid());
            }
            Ok(id)
        };
    let mut name = |id: &crate::shadow::ExprId,
                    resolution: NameResolution|
     -> Result<ResolvedExpr, HirAvailabilityError> {
        let expression = skeleton.expression(id).map_err(|_| invalid())?;
        let Form::Use { binder, .. } = expression.form() else {
            return Err(invalid());
        };
        let binder = skeleton.binder(binder).map_err(|_| invalid())?;
        Ok(ResolvedExpr::Name {
            occurrence: occurrence(expression)?,
            name: HirName {
                spelling: binder.name().to_owned(),
                range: expression.range().clone(),
            },
            resolution,
            range: expression.range().clone(),
        })
    };
    let callee = name(callee, NameResolution::Parameter(outer.clone()))?;
    let argument = name(argument, NameResolution::Parameter(x.clone()))?;
    let returned = skeleton.expression(returned).map_err(|_| invalid())?;
    let continuation = crate::shadow::ShadowLocalUse {
        occurrence: occurrence(returned)?,
        local: local.clone(),
        range: returned.range().clone(),
    };
    let apply = ResolvedExpr::Apply {
        occurrence: occurrence(call)?,
        source_form: *source_form,
        callee: Box::new(callee),
        argument: Box::new(argument),
        errors,
        range: call.range().clone(),
    };
    let initializer = ResolvedExpr::Lambda {
        occurrence: occurrence(lambda)?,
        parameter: x.clone(),
        body: Box::new(apply),
        range: lambda.range().clone(),
    };
    let body = crate::shadow::ShadowLocalBind {
        occurrence: occurrence(bound)?,
        local: local.clone(),
        initializer,
        continuation,
        captures: vec![outer.clone()].into_boxed_slice(),
        range: bound.range().clone(),
    };
    source.record_parameter(
        x.clone(),
        artifact
            .exact_source_key(
                skeleton
                    .binder(parameter)
                    .map_err(|_| invalid())?
                    .position(),
            )
            .map_err(|_| invalid())?,
    );
    source.record_local(
        local.clone(),
        artifact
            .exact_source_key(
                skeleton
                    .binder(input.local_binding())
                    .map_err(|_| invalid())?
                    .position(),
            )
            .map_err(|_| invalid())?,
    );
    source.local_parameter_owners.insert(x, local);
    source.local_binding = Some(body);
    hir.source_identity = Some(source);
    Ok(hir)
}
