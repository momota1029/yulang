//! Parse-owned declaration and import syntax for source-only export analysis.
//!
//! This module records syntax and identities only. Public export resolution
//! checks source routes and visibility, but assigns no type-level meaning.

use super::*;
use yu_syntax::SourceNodeKey;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceExportDeclaration {
    pub source: SourceNodeKey,
    pub kind: SyntaxKind,
    /// Module namespace for direct declarations, or the containing enum
    /// namespace for enum variants.
    pub namespace: Box<str>,
    pub name: Option<Box<str>>,
    pub public: bool,
    pub range: Range<usize>,
    pub text: Box<str>,
    pub recovered: bool,
}

/// A complete source-owned use declaration, including the original lossless
/// tree. Keeping the syntax nodes avoids inventing a flattened import meaning.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceUseDeclaration {
    pub source: SourceNodeKey,
    pub public: bool,
    pub range: Range<usize>,
    pub text: Box<str>,
    pub recovered: bool,
    pub tree: Vec<SourceUseTreeNode>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceUseTreeNode {
    pub source: SourceNodeKey,
    pub kind: SyntaxKind,
    pub range: Range<usize>,
    pub text: Box<str>,
    pub recovered: bool,
    pub children: Vec<SourceUseTreeNode>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceExportIndex {
    pub module: ModuleId,
    pub declarations: Vec<SourceExportDeclaration>,
    pub uses: Vec<SourceUseDeclaration>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SourceUseSelection {
    Name(Box<str>),
    Glob { exclusions: Vec<Box<str>> },
}

/// One leaf of a use tree, retaining both the declaration owner and leaf node.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceUseLeaf {
    pub declaration: SourceNodeKey,
    pub leaf: SourceNodeKey,
    pub public: bool,
    /// Complete route; named imports end in the selected declaration name,
    /// while glob imports contain only the target module route.
    pub path: Vec<Box<str>>,
    pub selection: SourceUseSelection,
    pub alias: Option<Box<str>>,
    pub recovered: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SourceUseFlattenError {
    Recovered(SourceNodeKey),
    UnsupportedShape(SourceNodeKey),
    InvalidPath(SourceNodeKey),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceExportResolution {
    pub module: Box<str>,
    pub name: Box<str>,
    pub declaration: SourceExportDeclaration,
    /// Public re-export leaves traversed from the requested module.
    pub route: Vec<SourceUseLeaf>,
}

/// Stable source identity for an exported declaration, independent of any
/// consumer HIR's local definition ordinal.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SourceExportId {
    pub module: Box<str>,
    pub name: Box<str>,
    pub source: SourceNodeKey,
    pub range: Range<usize>,
    pub kind: SyntaxKind,
}

impl SourceExportResolution {
    pub fn identity(&self) -> SourceExportId {
        SourceExportId {
            module: self.module.clone(),
            name: self.name.clone(),
            source: self.declaration.source.clone(),
            range: self.declaration.range.clone(),
            kind: self.declaration.kind,
        }
    }
}

/// One name imported from source modules. Ambiguity is retained at the name
/// use site and never converted to an arbitrary declaration choice.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SourceImportBinding {
    Resolved(SourceExportResolution),
    Ambiguous,
}

/// Parse-bound names supplied by one or more authenticated source modules.
/// The exact public routes are retained beside the exposed-name lookup.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceImportEnvironment {
    parse_root: SourceNodeKey,
    identity: ModuleIdentity,
    names: std::collections::HashMap<Box<str>, SourceImportBinding>,
    #[cfg(any(feature = "shadow", test))]
    role_ids: std::collections::HashMap<Box<str>, super::source_role::SourceRoleId>,
}

impl SourceImportEnvironment {
    pub(super) fn new(
        parse_root: SourceNodeKey,
        identity: ModuleIdentity,
        names: std::collections::HashMap<Box<str>, SourceImportBinding>,
    ) -> Self {
        Self {
            parse_root,
            identity,
            names,
            #[cfg(any(feature = "shadow", test))]
            role_ids: std::collections::HashMap::new(),
        }
    }

    pub fn parse_root(&self) -> &SourceNodeKey {
        &self.parse_root
    }

    pub fn identity(&self) -> &ModuleIdentity {
        &self.identity
    }

    pub fn names(&self) -> &std::collections::HashMap<Box<str>, SourceImportBinding> {
        &self.names
    }

    pub fn resolve(&self, name: &str) -> Option<&SourceImportBinding> {
        self.names.get(name)
    }

    /// Exact source declaration identity for an imported public role name.
    /// This is present only when the provider role index was authenticated.
    #[cfg(any(feature = "shadow", test))]
    pub fn role_id(&self, name: &str) -> Option<&super::source_role::SourceRoleId> {
        self.role_ids.get(name)
    }

    #[cfg(any(feature = "shadow", test))]
    pub(super) fn retain_role_ids(
        &mut self,
        role_ids: std::collections::HashMap<Box<str>, super::source_role::SourceRoleId>,
    ) {
        self.role_ids = role_ids;
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SourceExportResolveError {
    MissingModule(Box<str>),
    MissingExport {
        module: Box<str>,
        name: Box<str>,
    },
    Ambiguous {
        module: Box<str>,
        name: Box<str>,
    },
    Recovered {
        module: Box<str>,
        source: SourceNodeKey,
    },
    PrivateModule(Box<str>),
    UnsupportedUse {
        module: Box<str>,
        source: SourceNodeKey,
    },
    DuplicateModule(Box<str>),
    ResourceExhausted,
}

fn source_key(
    node: &SyntaxNode,
    counters: &LoweringCounters,
) -> Result<SourceNodeKey, HirAvailabilityError> {
    counters
        .source_nodes
        .get(node)
        .cloned()
        .ok_or(HirAvailabilityError::StructuralProjection)
}

fn use_tree(
    node: &SyntaxNode,
    counters: &LoweringCounters,
) -> Result<SourceUseTreeNode, HirAvailabilityError> {
    let mut children = Vec::new();
    for child in node.children() {
        children
            .try_reserve(1)
            .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        children.push(use_tree(&child, counters)?);
    }
    Ok(SourceUseTreeNode {
        source: source_key(node, counters)?,
        kind: node.kind(),
        range: crate::range_of(node),
        text: node.text().to_string().into_boxed_str(),
        recovered: has_recovery(node),
        children,
    })
}

fn declaration_name(node: &SyntaxNode) -> Option<Box<str>> {
    let text = node.text().to_string();
    if let Some(header) = text.trim_start().strip_prefix("pub host act ") {
        return header
            .split(':')
            .next()
            .map(str::trim)
            .filter(|name| !name.is_empty())
            .map(Into::into);
    }
    match node.kind() {
        SyntaxKind::ModDeclaration
        | SyntaxKind::StructDeclaration
        | SyntaxKind::EnumDeclaration
        | SyntaxKind::EnumVariant
        | SyntaxKind::ErrorDeclaration
        | SyntaxKind::TypeDeclaration
        | SyntaxKind::RoleDeclaration
        | SyntaxKind::ActDeclaration
        | SyntaxKind::BindingStatement => {}
        _ => return None,
    }
    node.descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::Identifier)
        .map(|token| token.text().to_owned().into_boxed_str())
}

fn host_act_members(
    root: &SyntaxNode,
    node: &SyntaxNode,
    module_namespace: &str,
    counters: &LoweringCounters,
) -> Result<Vec<SourceExportDeclaration>, HirAvailabilityError> {
    let range = crate::range_of(node);
    let source = root.text().to_string();
    let Some(header_end) = source[range.start..]
        .find('\n')
        .map(|offset| range.start + offset)
    else {
        return Ok(Vec::new());
    };
    let header = source[range.start..header_end].trim();
    let Some(name) = header
        .strip_prefix("pub host act ")
        .and_then(|tail| tail.split(':').next())
        .map(str::trim)
        .filter(|name| !name.is_empty())
    else {
        return Ok(Vec::new());
    };
    let namespace = format!("{module_namespace}::{name}");
    let owner = source_key(node, counters)?;
    let mut declarations = Vec::new();
    let mut cursor = header_end + 1;
    while cursor < source.len() {
        let line_end = source[cursor..]
            .find('\n')
            .map_or(source.len(), |offset| cursor + offset);
        let line = &source[cursor..line_end];
        let trimmed = line.trim();
        if trimmed.is_empty() {
            cursor = line_end.saturating_add(1);
            continue;
        }
        if line.len() == trimmed.len() {
            break;
        }
        if let Some(member) = trimmed.strip_prefix("pub ") {
            let name_end = member
                .find(|character: char| matches!(character, ':' | '(' | '=' | ' ' | '\t'))
                .unwrap_or(member.len());
            let member_name = &member[..name_end];
            if member_name.is_empty() {
                return Err(HirAvailabilityError::StructuralProjection);
            }
            let text_start = cursor + line.len() - trimmed.len();
            let text_end = text_start + trimmed.len();
            declarations
                .try_reserve(1)
                .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
            declarations.push(SourceExportDeclaration {
                source: owner.clone(),
                kind: SyntaxKind::ActDeclaration,
                namespace: namespace.clone().into(),
                name: Some(member_name.into()),
                public: true,
                range: text_start..text_end,
                text: source[text_start..text_end].into(),
                recovered: false,
            });
        }
        cursor = line_end.saturating_add(1);
    }
    Ok(declarations)
}

fn declaration(
    node: &SyntaxNode,
    namespace: &str,
    inherited_public: Option<bool>,
    counters: &LoweringCounters,
) -> Result<SourceExportDeclaration, HirAvailabilityError> {
    let public = inherited_public
        .unwrap_or_else(|| node.text().to_string().trim_start().starts_with("pub "));
    // A ModDeclaration's parser-owned Missing child is the unresolved external
    // module lookup. The resolver discharges that lookup against the supplied
    // exact child-module index; Error/Invalid still denote malformed syntax.
    let recovered = if node.kind() == SyntaxKind::ModDeclaration {
        node.descendants_with_tokens().any(|element| {
            element
                .as_node()
                .is_some_and(|node| node.kind() == SyntaxKind::Invalid)
                || element
                    .into_token()
                    .is_some_and(|token| token.kind() == SyntaxKind::Error)
        })
    } else {
        has_recovery(node)
    };
    Ok(SourceExportDeclaration {
        source: source_key(node, counters)?,
        kind: node.kind(),
        namespace: namespace.into(),
        name: declaration_name(node),
        public,
        range: crate::range_of(node),
        text: node.text().to_string().into_boxed_str(),
        recovered,
    })
}

pub(super) fn index(
    root: &SyntaxNode,
    module: &ModuleId,
    counters: &LoweringCounters,
) -> Result<SourceExportIndex, HirAvailabilityError> {
    let namespace = module_label(module).ok_or(HirAvailabilityError::StructuralProjection)?;
    let mut declarations = Vec::new();
    let mut uses = Vec::new();
    for item in root.children() {
        let mut top_level = vec![item.clone()];
        if item.kind() == SyntaxKind::Statement {
            top_level = item.children().collect();
        }
        for node in top_level {
            if node.kind() == SyntaxKind::UseDeclaration {
                let tree = node
                    .children()
                    .filter(|child| child.kind() == SyntaxKind::UseTree)
                    .map(|child| use_tree(&child, counters))
                    .collect::<Result<Vec<_>, _>>()?;
                let public = node.text().to_string().trim_start().starts_with("pub ");
                uses.try_reserve(1)
                    .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
                uses.push(SourceUseDeclaration {
                    source: source_key(&node, counters)?,
                    public,
                    range: crate::range_of(&node),
                    text: node.text().to_string().into_boxed_str(),
                    recovered: has_recovery(&node),
                    tree,
                });
            } else if matches!(
                node.kind(),
                SyntaxKind::ModDeclaration
                    | SyntaxKind::StructDeclaration
                    | SyntaxKind::EnumDeclaration
                    | SyntaxKind::ErrorDeclaration
                    | SyntaxKind::TypeDeclaration
                    | SyntaxKind::RoleDeclaration
                    | SyntaxKind::ActDeclaration
                    | SyntaxKind::BindingStatement
            ) {
                declarations
                    .try_reserve(1)
                    .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
                let direct = declaration(&node, &namespace, None, counters)?;
                let enum_namespace = (node.kind() == SyntaxKind::EnumDeclaration)
                    .then(|| format!("{}::{}", namespace, direct.name.as_deref().unwrap_or("")));
                let enum_public = direct.public;
                declarations.push(direct);
                if node
                    .text()
                    .to_string()
                    .trim_start()
                    .starts_with("pub host act ")
                {
                    let members = host_act_members(root, &node, &namespace, counters)?;
                    declarations
                        .try_reserve(members.len())
                        .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
                    declarations.extend(members);
                }
                if let Some(enum_namespace) = enum_namespace {
                    for variant in node
                        .descendants()
                        .filter(|child| child.kind() == SyntaxKind::EnumVariant)
                    {
                        declarations
                            .try_reserve(1)
                            .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
                        declarations.push(declaration(
                            &variant,
                            &enum_namespace,
                            Some(enum_public),
                            counters,
                        )?);
                    }
                }
            }
        }
    }
    Ok(SourceExportIndex {
        module: module.clone(),
        declarations,
        uses,
    })
}

fn append_path(
    path: &mut Vec<Box<str>>,
    node: &SourceUseTreeNode,
) -> Result<(), SourceUseFlattenError> {
    if node.kind != SyntaxKind::UsePath {
        return Err(SourceUseFlattenError::UnsupportedShape(node.source.clone()));
    }
    let text = node.text.trim();
    if text.is_empty() || text.contains('/') {
        return Err(SourceUseFlattenError::InvalidPath(node.source.clone()));
    }
    for segment in text.split("::") {
        if segment.is_empty() {
            return Err(SourceUseFlattenError::InvalidPath(node.source.clone()));
        }
        path.push(segment.into());
    }
    Ok(())
}

fn alias_of(nodes: &[&SourceUseTreeNode]) -> Result<Option<Box<str>>, SourceUseFlattenError> {
    let mut alias = None;
    for node in nodes
        .iter()
        .filter(|node| node.kind == SyntaxKind::UseAlias)
    {
        let Some(name) = node.text.trim().strip_prefix("as ").map(str::trim) else {
            return Err(SourceUseFlattenError::UnsupportedShape(node.source.clone()));
        };
        if name.is_empty() || alias.replace(Box::<str>::from(name)).is_some() {
            return Err(SourceUseFlattenError::UnsupportedShape(node.source.clone()));
        }
    }
    Ok(alias)
}

fn exclusion_names(
    node: &SourceUseTreeNode,
    names: &mut Vec<Box<str>>,
) -> Result<(), SourceUseFlattenError> {
    if node.kind == SyntaxKind::UseExclusion {
        let name = node.text.trim();
        if name.is_empty() || name.contains('/') {
            return Err(SourceUseFlattenError::UnsupportedShape(node.source.clone()));
        }
        names.push(name.into());
        return Ok(());
    }
    if node.kind != SyntaxKind::UseExclusionGroup {
        return Err(SourceUseFlattenError::UnsupportedShape(node.source.clone()));
    }
    for child in &node.children {
        if child.kind == SyntaxKind::UseExclusionGroup || child.kind == SyntaxKind::UseExclusion {
            exclusion_names(child, names)?;
        } else if child.kind != SyntaxKind::UseGroupForeignClose {
            return Err(SourceUseFlattenError::UnsupportedShape(
                child.source.clone(),
            ));
        }
    }
    Ok(())
}

fn flatten_tree(
    declaration: &SourceUseDeclaration,
    node: &SourceUseTreeNode,
    prefix: &[Box<str>],
    output: &mut Vec<SourceUseLeaf>,
) -> Result<(), SourceUseFlattenError> {
    if declaration.recovered || node.recovered {
        return Err(SourceUseFlattenError::Recovered(node.source.clone()));
    }
    if node.kind != SyntaxKind::UseTree {
        return Err(SourceUseFlattenError::UnsupportedShape(node.source.clone()));
    }
    let paths = node
        .children
        .iter()
        .filter(|child| child.kind == SyntaxKind::UsePath)
        .collect::<Vec<_>>();
    if paths.len() > 1 {
        return Err(SourceUseFlattenError::UnsupportedShape(node.source.clone()));
    }
    let mut path = prefix.to_vec();
    if let Some(path_node) = paths.first() {
        append_path(&mut path, path_node)?;
    }
    let groups = node
        .children
        .iter()
        .filter(|child| child.kind == SyntaxKind::UseGroup)
        .collect::<Vec<_>>();
    let globs = node
        .children
        .iter()
        .filter(|child| child.kind == SyntaxKind::UseGlob)
        .collect::<Vec<_>>();
    let controls = node
        .children
        .iter()
        .filter(|child| {
            matches!(
                child.kind,
                SyntaxKind::UseAlias | SyntaxKind::UseQualifiers | SyntaxKind::UseExclusionGroup
            )
        })
        .collect::<Vec<_>>();
    if groups.len() + globs.len() > 1 {
        return Err(SourceUseFlattenError::UnsupportedShape(node.source.clone()));
    }
    if let Some(group) = groups.first() {
        if !controls.is_empty() {
            return Err(SourceUseFlattenError::UnsupportedShape(node.source.clone()));
        }
        for child in &group.children {
            if child.kind == SyntaxKind::UseTree {
                flatten_tree(declaration, child, &path, output)?;
            } else if child.kind != SyntaxKind::UseGroupForeignClose {
                return Err(SourceUseFlattenError::UnsupportedShape(
                    child.source.clone(),
                ));
            }
        }
        return Ok(());
    }
    if let Some(glob) = globs.first() {
        if path.is_empty()
            || controls
                .iter()
                .any(|node| node.kind == SyntaxKind::UseQualifiers)
        {
            return Err(SourceUseFlattenError::UnsupportedShape(node.source.clone()));
        }
        let alias = alias_of(&glob.children.iter().collect::<Vec<_>>())?;
        let mut exclusions = Vec::new();
        for child in &glob.children {
            if child.kind == SyntaxKind::UseExclusionGroup {
                exclusion_names(child, &mut exclusions)?;
            } else if child.kind != SyntaxKind::UseAlias {
                return Err(SourceUseFlattenError::UnsupportedShape(
                    child.source.clone(),
                ));
            }
        }
        if controls
            .iter()
            .any(|node| node.kind != SyntaxKind::UseExclusionGroup)
        {
            return Err(SourceUseFlattenError::UnsupportedShape(node.source.clone()));
        }
        output.push(SourceUseLeaf {
            declaration: declaration.source.clone(),
            leaf: glob.source.clone(),
            public: declaration.public,
            path,
            selection: SourceUseSelection::Glob { exclusions },
            alias,
            recovered: false,
        });
        return Ok(());
    }
    if !globs.is_empty() || !groups.is_empty() || path.is_empty() {
        return Err(SourceUseFlattenError::UnsupportedShape(node.source.clone()));
    }
    let other_controls = controls
        .iter()
        .copied()
        .filter(|node| node.kind != SyntaxKind::UseQualifiers)
        .collect::<Vec<_>>();
    if controls
        .iter()
        .any(|node| node.kind == SyntaxKind::UseQualifiers)
    {
        return Err(SourceUseFlattenError::UnsupportedShape(node.source.clone()));
    }
    let alias = alias_of(&other_controls)?;
    let selected = path.pop().expect("nonempty path checked");
    path.push(selected.clone());
    output.push(SourceUseLeaf {
        declaration: declaration.source.clone(),
        leaf: node.source.clone(),
        public: declaration.public,
        path,
        selection: SourceUseSelection::Name(selected),
        alias,
        recovered: false,
    });
    Ok(())
}

/// Flattens groups while retaining the exact use declaration and leaf owners.
/// Unsupported/recovered grammar is an error, never an empty import set.
pub fn flatten_use_declaration(
    declaration: &SourceUseDeclaration,
) -> Result<Vec<SourceUseLeaf>, SourceUseFlattenError> {
    if declaration.recovered {
        return Err(SourceUseFlattenError::Recovered(declaration.source.clone()));
    }
    let mut output = Vec::new();
    for tree in &declaration.tree {
        flatten_tree(declaration, tree, &[], &mut output)?;
    }
    Ok(output)
}

fn module_label(module: &ModuleId) -> Option<Box<str>> {
    let path = module.file().key().normalized_workspace_relative_path();
    let path = path.strip_prefix("lib/").unwrap_or(path);
    let path = path.strip_suffix(".yu")?;
    if path.is_empty() || path.starts_with('/') || path.split('/').any(str::is_empty) {
        return None;
    }
    Some(path.replace('/', "::").into_boxed_str())
}

fn flatten_error_for_resolver(
    module: &str,
    error: SourceUseFlattenError,
) -> SourceExportResolveError {
    match error {
        SourceUseFlattenError::Recovered(source) => SourceExportResolveError::Recovered {
            module: module.into(),
            source,
        },
        SourceUseFlattenError::UnsupportedShape(source)
        | SourceUseFlattenError::InvalidPath(source) => SourceExportResolveError::UnsupportedUse {
            module: module.into(),
            source,
        },
    }
}

fn validate_public_module_path(
    modules: &std::collections::HashMap<Box<str>, &SourceExportIndex>,
    module: &str,
) -> Result<(), SourceExportResolveError> {
    let segments = module.split("::").collect::<Vec<_>>();
    if segments.is_empty() || segments.iter().any(|segment| segment.is_empty()) {
        return Err(SourceExportResolveError::MissingModule(module.into()));
    }
    for depth in 2..=segments.len() {
        let parent = segments[..depth - 1].join("::");
        let child_module = segments[..depth].join("::");
        let Some(parent_index) = modules.get(parent.as_str()).copied() else {
            return Err(SourceExportResolveError::MissingModule(parent.into()));
        };
        let mut declarations = parent_index.declarations.iter().filter(|declaration| {
            declaration.kind == SyntaxKind::ModDeclaration
                && declaration.namespace.as_ref() == parent
                && declaration.name.as_deref() == Some(segments[depth - 1])
        });
        let Some(declaration) = declarations.next() else {
            return Err(SourceExportResolveError::MissingModule(child_module.into()));
        };
        if declaration.recovered {
            return Err(SourceExportResolveError::Recovered {
                module: parent.into(),
                source: declaration.source.clone(),
            });
        }
        if declarations.next().is_some() {
            return Err(SourceExportResolveError::Ambiguous {
                module: parent.into(),
                name: segments[depth - 1].into(),
            });
        }
        if !declaration.public {
            return Err(SourceExportResolveError::PrivateModule(child_module.into()));
        }
    }
    Ok(())
}

fn resolve_walk(
    modules: &std::collections::HashMap<Box<str>, &SourceExportIndex>,
    module: &str,
    name: &str,
    route: &[SourceUseLeaf],
    visited: &mut std::collections::HashSet<(Box<str>, Box<str>)>,
    matches: &mut Vec<SourceExportResolution>,
) -> Result<(), SourceExportResolveError> {
    let visit = (module.into(), name.into());
    if !visited.insert(visit) {
        return Ok(());
    }
    let index = modules.get(module).copied();
    let virtual_namespace = modules.values().any(|candidate| {
        candidate.declarations.iter().any(|declaration| {
            (declaration.kind == SyntaxKind::EnumVariant
                && declaration.namespace.as_ref() == module)
                || (declaration.kind == SyntaxKind::ActDeclaration
                    && declaration.namespace.as_ref() == module)
                || (declaration.kind == SyntaxKind::BindingStatement
                    && declaration.text.trim_start().starts_with("pub host act ")
                    && declaration
                        .name
                        .as_deref()
                        .is_some_and(|name| format!("{}::{name}", declaration.namespace) == module))
        })
    });
    if index.is_none() && !virtual_namespace {
        return Err(SourceExportResolveError::MissingModule(module.into()));
    }
    if index.is_some() {
        validate_public_module_path(modules, module)?;
    } else if let Some((parent, _)) = module.rsplit_once("::") {
        validate_public_module_path(modules, parent)?;
    }

    for declaration in modules
        .values()
        .flat_map(|candidate| candidate.declarations.iter())
        .filter(|declaration| declaration.namespace.as_ref() == module)
    {
        if !declaration.public {
            continue;
        }
        if declaration.recovered
            && declaration
                .name
                .as_deref()
                .map_or(true, |found| found == name)
        {
            return Err(SourceExportResolveError::Recovered {
                module: module.into(),
                source: declaration.source.clone(),
            });
        }
        if declaration.name.as_deref() == Some(name) {
            matches.push(SourceExportResolution {
                module: module.into(),
                name: name.into(),
                declaration: declaration.clone(),
                route: route.to_vec(),
            });
        }
    }

    for use_declaration in index.into_iter().flat_map(|index| index.uses.iter()) {
        if !use_declaration.public {
            continue;
        }
        let leaves = flatten_use_declaration(use_declaration)
            .map_err(|error| flatten_error_for_resolver(module, error))?;
        for leaf in leaves {
            let target = match &leaf.selection {
                SourceUseSelection::Name(selected) => {
                    if leaf.alias.as_deref().unwrap_or(selected) != name {
                        continue;
                    }
                    let Some((_, target_segments)) = leaf.path.split_last() else {
                        return Err(SourceExportResolveError::UnsupportedUse {
                            module: module.into(),
                            source: leaf.leaf.clone(),
                        });
                    };
                    if target_segments.is_empty() {
                        // Single-segment imports may name an item in the current module.
                        module.to_owned()
                    } else {
                        let target = target_segments
                            .iter()
                            .map(AsRef::as_ref)
                            .collect::<Vec<_>>()
                            .join("::");
                        if target_segments
                            .first()
                            .is_some_and(|segment| segment.as_ref() == "std")
                        {
                            target
                        } else {
                            format!("{module}::{target}")
                        }
                    }
                }
                SourceUseSelection::Glob { exclusions } => {
                    if leaf.alias.is_some() {
                        return Err(SourceExportResolveError::UnsupportedUse {
                            module: module.into(),
                            source: leaf.leaf.clone(),
                        });
                    }
                    if exclusions.iter().any(|excluded| excluded.as_ref() == name) {
                        continue;
                    }
                    let target = leaf
                        .path
                        .iter()
                        .map(AsRef::as_ref)
                        .collect::<Vec<_>>()
                        .join("::");
                    if leaf
                        .path
                        .first()
                        .is_some_and(|segment| segment.as_ref() == "std")
                    {
                        target
                    } else {
                        format!("{module}::{target}")
                    }
                }
            };
            let mut next_route = route.to_vec();
            next_route.push(leaf);
            resolve_walk(modules, &target, name, &next_route, visited, matches)?;
        }
    }
    Ok(())
}

/// Resolves a public name to one unique parse-owned declaration over a finite
/// set of module indexes. Cycles terminate, and distinct source declarations
/// remain ambiguous even when their spelling is identical.
pub fn resolve_public_export(
    indexes: &[SourceExportIndex],
    module: &str,
    name: &str,
) -> Result<SourceExportResolution, SourceExportResolveError> {
    let mut modules = std::collections::HashMap::new();
    modules
        .try_reserve(indexes.len())
        .map_err(|_| SourceExportResolveError::ResourceExhausted)?;
    for index in indexes {
        let label = module_label(&index.module)
            .ok_or_else(|| SourceExportResolveError::MissingModule(module.into()))?;
        if modules.insert(label.clone(), index).is_some() {
            return Err(SourceExportResolveError::DuplicateModule(label));
        }
    }
    if !modules.contains_key(module) {
        return Err(SourceExportResolveError::MissingModule(module.into()));
    }
    validate_public_module_path(&modules, module)?;
    let mut visited = std::collections::HashSet::new();
    let mut matches = Vec::new();
    resolve_walk(&modules, module, name, &[], &mut visited, &mut matches)?;
    let mut distinct = Vec::new();
    for candidate in matches {
        if !distinct.iter().any(|found: &SourceExportResolution| {
            found.module == candidate.module
                && found.declaration.source == candidate.declaration.source
                && found.declaration.range == candidate.declaration.range
        }) {
            distinct.push(candidate);
        }
    }
    match distinct.len() {
        0 => Err(SourceExportResolveError::MissingExport {
            module: module.into(),
            name: name.into(),
        }),
        1 => Ok(distinct.pop().expect("one resolution")),
        _ => Err(SourceExportResolveError::Ambiguous {
            module: module.into(),
            name: name.into(),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    #[test]
    fn public_declarations_and_use_tree_keep_parse_owned_structure() {
        let text = "pub role Display 'a:\n    pub a.show: str\npub use std::core::fmt::{Display}\npub use std::core::fmt::*\npub use std::core::fmt::Display as D\n";
        let source: Arc<yu_syntax::SourceText> = Arc::from(text);
        let parsed = yu_syntax::parse_file(
            source.clone(),
            Arc::new(yu_syntax::scan_header(source)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        let module = ModuleIdentity::source_root(FileId::new(FileKey::new("exports", "m.yu")));
        let mut counters = LoweringCounters::default();
        counters.source_nodes = crate::source_identity::try_source_keys(&parsed).unwrap();
        let root = SyntaxNode::new_root(parsed.green().clone());
        let index = super::index(&root, module.module(), &counters).unwrap();

        let role = index
            .declarations
            .iter()
            .find(|item| item.kind == SyntaxKind::RoleDeclaration)
            .unwrap();
        assert_eq!(role.name.as_deref(), Some("Display"));
        assert!(role.public);
        assert_eq!(&text[role.range.clone()], role.text.as_ref());

        assert_eq!(index.uses.len(), 3);
        assert!(
            index
                .uses
                .iter()
                .all(|use_decl| use_decl.public && !use_decl.recovered)
        );
        fn kinds(node: &SourceUseTreeNode, output: &mut Vec<SyntaxKind>) {
            output.push(node.kind);
            for child in &node.children {
                kinds(child, output);
            }
        }
        let mut observed = Vec::new();
        for use_decl in &index.uses {
            assert_eq!(&text[use_decl.range.clone()], use_decl.text.as_ref());
            for node in &use_decl.tree {
                kinds(node, &mut observed);
            }
        }
        for kind in [
            SyntaxKind::UsePath,
            SyntaxKind::UseGroup,
            SyntaxKind::UseAlias,
            SyntaxKind::UseGlob,
        ] {
            assert!(observed.contains(&kind), "missing {kind:?}: {observed:?}");
        }
        let group = flatten_use_declaration(&index.uses[0]).unwrap();
        assert_eq!(group.len(), 1);
        assert_eq!(
            group[0].path.iter().map(AsRef::as_ref).collect::<Vec<_>>(),
            ["std", "core", "fmt", "Display"]
        );
        assert_eq!(
            group[0].selection,
            SourceUseSelection::Name("Display".into())
        );
        let glob = flatten_use_declaration(&index.uses[1]).unwrap();
        assert_eq!(
            glob[0].path.iter().map(AsRef::as_ref).collect::<Vec<_>>(),
            ["std", "core", "fmt"]
        );
        assert_eq!(
            glob[0].selection,
            SourceUseSelection::Glob {
                exclusions: Vec::new()
            }
        );
        let alias = flatten_use_declaration(&index.uses[2]).unwrap();
        assert_eq!(
            alias[0].path.iter().map(AsRef::as_ref).collect::<Vec<_>>(),
            ["std", "core", "fmt", "Display"]
        );
        assert_eq!(alias[0].alias.as_deref(), Some("D"));
        for node in index.uses.iter().flat_map(|use_decl| &use_decl.tree) {
            fn check_ranges(node: &SourceUseTreeNode, source: &str) {
                assert_eq!(source.get(node.range.clone()), Some(node.text.as_ref()));
                for child in &node.children {
                    check_ranges(child, source);
                }
            }
            check_ranges(node, text);
        }
    }

    #[test]
    fn public_export_resolution_distinguishes_private_ambiguous_and_recovered_routes() {
        fn index(path: &str, text: &str) -> SourceExportIndex {
            let source: Arc<yu_syntax::SourceText> = Arc::from(text);
            let parsed = yu_syntax::parse_file(
                source.clone(),
                Arc::new(yu_syntax::scan_header(source)),
                Arc::new(yu_syntax::SyntaxEnvironment::empty()),
            );
            let module = ModuleIdentity::source_root(FileId::new(FileKey::new("exports", path)));
            let mut counters = LoweringCounters::default();
            counters.source_nodes = crate::source_identity::try_source_keys(&parsed).unwrap();
            let root = SyntaxNode::new_root(parsed.green().clone());
            super::index(&root, module.module(), &counters).unwrap()
        }

        let root = index("lib/std.yu", "pub mod a;\npub mod b;\npub mod c;\n");
        let a = index("lib/std/a.yu", "pub role Foo 'a:\n    pub a.foo: str\n");
        let b_private = index("lib/std/b.yu", "use std::a::*\n");
        assert_eq!(
            resolve_public_export(&[root.clone(), a.clone(), b_private], "std::b", "Foo"),
            Err(SourceExportResolveError::MissingExport {
                module: "std::b".into(),
                name: "Foo".into(),
            })
        );

        let b_public = index(
            "lib/std/b.yu",
            "pub use std::a::*\npub role Foo 'b:\n    pub b.foo: str\n",
        );
        assert!(matches!(
            resolve_public_export(&[root.clone(), a.clone(), b_public], "std::b", "Foo"),
            Err(SourceExportResolveError::Ambiguous { .. })
        ));

        let recovered = index("lib/std/c.yu", "pub use std::a::{Foo\n");
        assert!(matches!(
            resolve_public_export(&[root.clone(), a, recovered], "std::c", "Foo"),
            Err(SourceExportResolveError::Recovered { .. })
        ));
    }

    #[test]
    fn public_export_resolution_rejects_private_module_ancestors() {
        fn index(path: &str, text: &str) -> SourceExportIndex {
            let source: Arc<yu_syntax::SourceText> = Arc::from(text);
            let parsed = yu_syntax::parse_file(
                source.clone(),
                Arc::new(yu_syntax::scan_header(source)),
                Arc::new(yu_syntax::SyntaxEnvironment::empty()),
            );
            let module = ModuleIdentity::source_root(FileId::new(FileKey::new("exports", path)));
            let mut counters = LoweringCounters::default();
            counters.source_nodes = crate::source_identity::try_source_keys(&parsed).unwrap();
            let root = SyntaxNode::new_root(parsed.green().clone());
            let index = super::index(&root, module.module(), &counters).unwrap();
            index
        }

        let root = index("lib/std.yu", "mod hidden;\n");
        let hidden = index(
            "lib/std/hidden.yu",
            "pub role Foo 'a:\n    pub a.foo: str\n",
        );
        assert_eq!(
            resolve_public_export(&[root, hidden], "std::hidden", "Foo"),
            Err(SourceExportResolveError::PrivateModule(
                "std::hidden".into()
            ))
        );
    }

    #[test]
    fn public_export_resolution_terminates_on_reexport_cycles() {
        fn index(path: &str, text: &str) -> SourceExportIndex {
            let source: Arc<yu_syntax::SourceText> = Arc::from(text);
            let parsed = yu_syntax::parse_file(
                source.clone(),
                Arc::new(yu_syntax::scan_header(source)),
                Arc::new(yu_syntax::SyntaxEnvironment::empty()),
            );
            let module = ModuleIdentity::source_root(FileId::new(FileKey::new("exports", path)));
            let mut counters = LoweringCounters::default();
            counters.source_nodes = crate::source_identity::try_source_keys(&parsed).unwrap();
            let root = SyntaxNode::new_root(parsed.green().clone());
            super::index(&root, module.module(), &counters).unwrap()
        }

        let root = index("lib/std.yu", "pub mod a;\npub mod b;\n");
        let a = index("lib/std/a.yu", "pub use std::b::*\n");
        let b = index("lib/std/b.yu", "pub use std::a::*\n");
        assert_eq!(
            resolve_public_export(&[root, a, b], "std::a", "Missing"),
            Err(SourceExportResolveError::MissingExport {
                module: "std::a".into(),
                name: "Missing".into(),
            })
        );
    }
}
