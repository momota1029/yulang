//! Parse-owned declaration and import syntax for source-only export analysis.
//!
//! This module records syntax and identities only. It does not grant visibility
//! or resolve an imported name; callers must do that from these retained facts.

use super::*;
use yu_syntax::SourceNodeKey;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceExportDeclaration {
    pub source: SourceNodeKey,
    pub kind: SyntaxKind,
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
    match node.kind() {
        SyntaxKind::ModDeclaration
        | SyntaxKind::StructDeclaration
        | SyntaxKind::EnumDeclaration
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

fn declaration(
    node: &SyntaxNode,
    counters: &LoweringCounters,
) -> Result<SourceExportDeclaration, HirAvailabilityError> {
    let public = node.text().to_string().trim_start().starts_with("pub ");
    Ok(SourceExportDeclaration {
        source: source_key(node, counters)?,
        kind: node.kind(),
        name: declaration_name(node),
        public,
        range: crate::range_of(node),
        text: node.text().to_string().into_boxed_str(),
        recovered: has_recovery(node),
    })
}

pub(super) fn index(
    root: &SyntaxNode,
    module: &ModuleId,
    counters: &LoweringCounters,
) -> Result<SourceExportIndex, HirAvailabilityError> {
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
                declarations.push(declaration(&node, counters)?);
            }
        }
    }
    Ok(SourceExportIndex {
        module: module.clone(),
        declarations,
        uses,
    })
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
}
