use rowan::NodeOrToken;
use yulang_parser::lex::SyntaxKind;

use crate::symbols::{Name, Path, Visibility as ModuleVisibility};

use super::super::has_token;
use crate::lower::{LowerState, SyntaxNode};

/// `use` 宣言を lowering する。
///
/// - `use a::*` は現在の lexical search に module を追加する
/// - `pub use a::b` は現在 module に value/type/module alias を登録する
/// - `use a::b as c` は現在 module に `c` alias を登録する
pub(crate) fn lower_use_decl(state: &mut LowerState, node: &SyntaxNode) {
    let visibility = use_visibility(node);
    for import in use_decl_imports(node) {
        match import {
            UseImport::Alias { name, path } => {
                import_alias(state, name, &path, visibility);
            }
            UseImport::Glob { prefix, excluded } => {
                state.ctx.add_use(&prefix);
                if visibility != UseVisibility::My {
                    import_glob_reexports(state, &prefix, &excluded, visibility);
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum UseImport {
    Alias { name: Name, path: Path },
    Glob { prefix: Path, excluded: Vec<Name> },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum UseVisibility {
    My,
    Our,
    Pub,
}

fn use_visibility(node: &SyntaxNode) -> UseVisibility {
    if has_token(node, SyntaxKind::Pub) {
        UseVisibility::Pub
    } else if has_token(node, SyntaxKind::Our) {
        UseVisibility::Our
    } else {
        UseVisibility::My
    }
}

fn import_alias(state: &mut LowerState, name: Name, path: &Path, visibility: UseVisibility) {
    let module_visibility = use_module_visibility(visibility);
    if let Some(def) = state.ctx.resolve_path_value(path) {
        state.insert_value_alias_with_visibility(
            state.ctx.current_module,
            name.clone(),
            def,
            module_visibility,
        );
    }
    if let Some(def) = state.ctx.resolve_path_type(path) {
        state.insert_type_alias_with_visibility(
            state.ctx.current_module,
            name.clone(),
            def,
            module_visibility,
        );
    }
    if let Some(module) = state.ctx.resolve_module_path(path) {
        state.insert_module_alias_with_visibility(
            state.ctx.current_module,
            name,
            module,
            module_visibility,
        );
    }
}

fn import_glob_reexports(
    state: &mut LowerState,
    prefix: &Path,
    excluded: &[Name],
    visibility: UseVisibility,
) {
    let Some(module) = state.ctx.resolve_module_path(prefix) else {
        return;
    };
    let node = state.ctx.modules.node(module);
    let module_visibility = use_module_visibility(visibility);
    let values = node
        .values
        .iter()
        .filter(|(name, _)| !excluded.contains(name))
        .map(|(name, def)| (name.clone(), *def))
        .collect::<Vec<_>>();
    let operators = node
        .operator_values
        .iter()
        .filter(|((name, _), _)| !excluded.contains(name))
        .map(|((name, fixity), def)| (name.clone(), *fixity, *def))
        .collect::<Vec<_>>();
    let types = node
        .types
        .iter()
        .filter(|(name, _)| !excluded.contains(name))
        .map(|(name, def)| (name.clone(), *def))
        .collect::<Vec<_>>();
    let modules = node
        .modules
        .iter()
        .filter(|(name, _)| !excluded.contains(name))
        .map(|(name, module)| (name.clone(), *module))
        .collect::<Vec<_>>();

    for (name, def) in values {
        state.insert_value_alias_with_visibility(
            state.ctx.current_module,
            name,
            def,
            module_visibility,
        );
    }
    for (name, fixity, def) in operators {
        if state
            .ctx
            .modules
            .node(state.ctx.current_module)
            .operator_values
            .contains_key(&(name.clone(), fixity))
        {
            continue;
        }
        state.ctx.modules.insert_operator_value_with_visibility(
            state.ctx.current_module,
            name,
            fixity,
            def,
            module_visibility,
        );
    }
    for (name, def) in types {
        state.insert_type_alias_with_visibility(
            state.ctx.current_module,
            name,
            def,
            module_visibility,
        );
    }
    for (name, module) in modules {
        state.insert_module_alias_with_visibility(
            state.ctx.current_module,
            name,
            module,
            module_visibility,
        );
    }
}

fn use_module_visibility(visibility: UseVisibility) -> ModuleVisibility {
    match visibility {
        UseVisibility::My => ModuleVisibility::My,
        UseVisibility::Our => ModuleVisibility::Our,
        UseVisibility::Pub => ModuleVisibility::Pub,
    }
}

fn use_decl_imports(node: &SyntaxNode) -> Vec<UseImport> {
    let mut path = Vec::new();
    let mut after_as = false;
    let mut alias = None;
    let mut imports = Vec::new();
    let mut excluding_glob = None;

    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Token(tok) => match tok.kind() {
                SyntaxKind::Pub | SyntaxKind::Our | SyntaxKind::My | SyntaxKind::Use => {}
                SyntaxKind::ColonColon | SyntaxKind::Slash => {}
                SyntaxKind::Ident if tok.text() == "without" => {
                    excluding_glob = imports.len().checked_sub(1);
                    path.clear();
                    alias = None;
                    after_as = false;
                }
                SyntaxKind::Ident if excluding_glob.is_some() => {
                    push_use_glob_exclusion(
                        &mut imports,
                        excluding_glob,
                        Name(tok.text().to_string()),
                    );
                }
                SyntaxKind::Ident if after_as => {
                    alias = Some(Name(tok.text().to_string()));
                    after_as = false;
                }
                SyntaxKind::Ident => path.push(Name(tok.text().to_string())),
                SyntaxKind::As => after_as = true,
                SyntaxKind::OpName if tok.text() == "*" => {
                    imports.push(UseImport::Glob {
                        prefix: Path {
                            segments: path.clone(),
                        },
                        excluded: Vec::new(),
                    });
                    path.clear();
                    alias = None;
                    after_as = false;
                }
                SyntaxKind::OpName if excluding_glob.is_some() => {
                    push_use_glob_exclusion(
                        &mut imports,
                        excluding_glob,
                        Name(tok.text().to_string()),
                    );
                }
                SyntaxKind::OpName => path.push(Name(tok.text().to_string())),
                SyntaxKind::ParenL | SyntaxKind::ParenR => {}
                _ => {}
            },
            NodeOrToken::Node(child) if child.kind() == SyntaxKind::BraceGroup => {
                if excluding_glob.is_some() {
                    collect_use_glob_exclusions(&child, &mut imports, excluding_glob);
                } else {
                    collect_use_group_imports(&child, &path, &mut imports);
                    path.clear();
                    alias = None;
                    after_as = false;
                }
            }
            _ => {}
        }
    }

    push_use_alias_import(path, alias, &mut imports);
    imports
}

fn collect_use_group_imports(node: &SyntaxNode, base: &[Name], imports: &mut Vec<UseImport>) {
    let mut path = base.to_vec();
    let mut alias = None;
    let mut after_as = false;
    let mut consumed_nested = false;
    let mut excluding_glob = None;

    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Token(tok) => match tok.kind() {
                SyntaxKind::BraceL => {}
                SyntaxKind::BraceR => {
                    if !consumed_nested {
                        push_use_alias_import(path, alias.take(), imports);
                    }
                    return;
                }
                SyntaxKind::Comma => {
                    if !consumed_nested {
                        push_use_alias_import(path, alias.take(), imports);
                    }
                    path = base.to_vec();
                    after_as = false;
                    consumed_nested = false;
                }
                SyntaxKind::ColonColon | SyntaxKind::Slash => {}
                SyntaxKind::Ident if tok.text() == "without" => {
                    excluding_glob = imports.len().checked_sub(1);
                    path = base.to_vec();
                    alias = None;
                    after_as = false;
                    consumed_nested = true;
                }
                SyntaxKind::Ident if excluding_glob.is_some() => {
                    push_use_glob_exclusion(
                        &mut *imports,
                        excluding_glob,
                        Name(tok.text().to_string()),
                    );
                    consumed_nested = true;
                }
                SyntaxKind::Ident if after_as => {
                    alias = Some(Name(tok.text().to_string()));
                    after_as = false;
                }
                SyntaxKind::Ident => path.push(Name(tok.text().to_string())),
                SyntaxKind::As => after_as = true,
                SyntaxKind::OpName if tok.text() == "*" => {
                    imports.push(UseImport::Glob {
                        prefix: Path {
                            segments: path.clone(),
                        },
                        excluded: Vec::new(),
                    });
                    path = base.to_vec();
                    alias = None;
                    after_as = false;
                    consumed_nested = true;
                }
                SyntaxKind::OpName if excluding_glob.is_some() => {
                    push_use_glob_exclusion(
                        &mut *imports,
                        excluding_glob,
                        Name(tok.text().to_string()),
                    );
                    consumed_nested = true;
                }
                SyntaxKind::OpName => path.push(Name(tok.text().to_string())),
                SyntaxKind::ParenL | SyntaxKind::ParenR => {}
                _ => {}
            },
            NodeOrToken::Node(child) if child.kind() == SyntaxKind::BraceGroup => {
                if excluding_glob.is_some() {
                    collect_use_glob_exclusions(&child, imports, excluding_glob);
                } else {
                    collect_use_group_imports(&child, &path, imports);
                }
                path = base.to_vec();
                alias = None;
                after_as = false;
                consumed_nested = true;
            }
            NodeOrToken::Node(child) if child.kind() == SyntaxKind::Separator => {
                if !consumed_nested {
                    push_use_alias_import(path, alias.take(), imports);
                }
                path = base.to_vec();
                after_as = false;
                consumed_nested = false;
            }
            _ => {}
        }
    }

    if !consumed_nested {
        push_use_alias_import(path, alias, imports);
    }
}

fn collect_use_glob_exclusions(
    node: &SyntaxNode,
    imports: &mut Vec<UseImport>,
    glob_idx: Option<usize>,
) {
    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Token(tok) => match tok.kind() {
                SyntaxKind::Ident => {
                    push_use_glob_exclusion(imports, glob_idx, Name(tok.text().to_string()));
                }
                SyntaxKind::OpName if tok.text() != "*" => {
                    push_use_glob_exclusion(imports, glob_idx, Name(tok.text().to_string()));
                }
                _ => {}
            },
            NodeOrToken::Node(child) if child.kind() == SyntaxKind::BraceGroup => {
                collect_use_glob_exclusions(&child, imports, glob_idx);
            }
            _ => {}
        }
    }
}

fn push_use_glob_exclusion(imports: &mut [UseImport], glob_idx: Option<usize>, name: Name) {
    let Some(idx) = glob_idx else {
        return;
    };
    let Some(UseImport::Glob { excluded, .. }) = imports.get_mut(idx) else {
        return;
    };
    if !excluded.contains(&name) {
        excluded.push(name);
    }
}

fn push_use_alias_import(path: Vec<Name>, alias: Option<Name>, imports: &mut Vec<UseImport>) {
    if path.is_empty() {
        return;
    }
    let Some(name) = alias.or_else(|| path.last().cloned()) else {
        return;
    };
    imports.push(UseImport::Alias {
        name,
        path: Path { segments: path },
    });
}
