//! act が参照する strict type expression を解決する。
//!
//! これは型注釈ではない。`AnnType` は上下からの抑え込みや effect row の引き算を背負うが、
//! act 解決では「どの act 型を参照しているか」と、その厳格な型引数だけを読む。

use poly::types::BuiltinType;
use rowan::{NodeOrToken, SyntaxNode};
use sources::Name;
use yulang_parser::lex::SyntaxKind;
use yulang_parser::sink::YulangLanguage;

use crate::{ModuleId, ModuleOrder, ModuleTable, ModuleTypeDecl, ModuleTypeKind, TypeDeclId};

type Cst = SyntaxNode<YulangLanguage>;
type CstItem = NodeOrToken<Cst, rowan::SyntaxToken<YulangLanguage>>;

pub(crate) struct ActTypeResolver<'a> {
    modules: &'a ModuleTable,
    module: ModuleId,
    site: ModuleOrder,
}

impl<'a> ActTypeResolver<'a> {
    pub(crate) fn new(modules: &'a ModuleTable, module: ModuleId, site: ModuleOrder) -> Self {
        Self {
            modules,
            module,
            site,
        }
    }

    pub(crate) fn resolve_act_use(
        &self,
        type_expr: &Cst,
    ) -> Result<ResolvedActUse, ActTypeResolveError> {
        let ty = self.build_type_expr(type_expr)?;
        let (act, args) = act_use_head(ty.clone())
            .ok_or(ActTypeResolveError::InvalidActHead { ty: ty.clone() })?;
        let decl = self
            .modules
            .type_decl_by_id(act)
            .ok_or(ActTypeResolveError::UnresolvedTypeId { id: act })?;
        if decl.kind != ModuleTypeKind::Act {
            return Err(ActTypeResolveError::InvalidActHead { ty });
        }
        Ok(ResolvedActUse { decl, args })
    }

    fn build_type_expr(&self, type_expr: &Cst) -> Result<ActTypeExpr, ActTypeResolveError> {
        if type_expr.kind() != SyntaxKind::TypeExpr {
            return Err(ActTypeResolveError::ExpectedTypeExpr {
                kind: type_expr.kind(),
            });
        }
        if let Some(arrow) = type_expr
            .children()
            .find(|child| child.kind() == SyntaxKind::TypeArrow)
        {
            if let Some(row) = arrow
                .children()
                .find(|child| child.kind() == SyntaxKind::TypeRow)
            {
                return Err(ActTypeResolveError::UnsupportedSyntax { kind: row.kind() });
            }
            let param = self.build_type_head(type_expr)?;
            let ret = arrow
                .children()
                .find(|child| child.kind() == SyntaxKind::TypeExpr)
                .ok_or(ActTypeResolveError::MissingFunctionReturn)?;
            return Ok(ActTypeExpr::Function {
                param: Box::new(param),
                ret: Box::new(self.build_type_expr(&ret)?),
            });
        }

        self.build_type_head(type_expr)
    }

    fn build_type_head(&self, type_expr: &Cst) -> Result<ActTypeExpr, ActTypeResolveError> {
        let items = type_expr
            .children_with_tokens()
            .filter(|item| !item_is_trivia(item))
            .filter(|item| {
                !matches!(item, NodeOrToken::Node(node) if node.kind() == SyntaxKind::TypeArrow)
            })
            .collect::<Vec<_>>();

        let Some(first) = items.first() else {
            return Err(ActTypeResolveError::EmptyTypeExpr);
        };
        let (base, next) = self.build_type_base(&items, first)?;
        self.build_type_applications(base, &items[next..])
    }

    fn build_type_base(
        &self,
        items: &[CstItem],
        first: &CstItem,
    ) -> Result<(ActTypeExpr, usize), ActTypeResolveError> {
        match first {
            NodeOrToken::Token(token) if token.kind() == SyntaxKind::Ident => {
                let (path, next) = parse_type_path_prefix(items)?;
                Ok((self.resolve_type_path(path)?, next))
            }
            NodeOrToken::Token(token) if token.kind() == SyntaxKind::SigilIdent => {
                Ok((ActTypeExpr::Var(type_var_name(token.text())), 1))
            }
            NodeOrToken::Token(token) => {
                Err(ActTypeResolveError::UnsupportedSyntax { kind: token.kind() })
            }
            NodeOrToken::Node(node) if node.kind() == SyntaxKind::TypeParenGroup => {
                Ok((self.build_type_paren_group(node)?, 1))
            }
            NodeOrToken::Node(node) => {
                Err(ActTypeResolveError::UnsupportedSyntax { kind: node.kind() })
            }
        }
    }

    fn build_type_applications(
        &self,
        base: ActTypeExpr,
        suffixes: &[CstItem],
    ) -> Result<ActTypeExpr, ActTypeResolveError> {
        let mut args = Vec::new();
        for item in suffixes {
            let NodeOrToken::Node(node) = item else {
                let kind = item
                    .as_token()
                    .map(|token| token.kind())
                    .unwrap_or(SyntaxKind::TypeExpr);
                return Err(ActTypeResolveError::UnsupportedSyntax { kind });
            };
            match node.kind() {
                SyntaxKind::TypeApply => args.push(self.build_single_type_arg(node)?),
                SyntaxKind::TypeCall => {
                    let call_args = node
                        .children()
                        .filter(|child| child.kind() == SyntaxKind::TypeExpr)
                        .map(|child| self.build_type_expr(&child))
                        .collect::<Result<Vec<_>, _>>()?;
                    if call_args.is_empty() {
                        return Err(ActTypeResolveError::UnsupportedSyntax { kind: node.kind() });
                    }
                    args.extend(call_args);
                }
                _ => return Err(ActTypeResolveError::UnsupportedSyntax { kind: node.kind() }),
            }
        }

        if args.is_empty() {
            Ok(base)
        } else {
            Ok(ActTypeExpr::Apply {
                callee: Box::new(base),
                args,
            })
        }
    }

    fn build_single_type_arg(&self, apply: &Cst) -> Result<ActTypeExpr, ActTypeResolveError> {
        let children = apply
            .children()
            .filter(|child| child.kind() == SyntaxKind::TypeExpr)
            .collect::<Vec<_>>();
        let [child] = children.as_slice() else {
            return Err(ActTypeResolveError::UnsupportedSyntax { kind: apply.kind() });
        };
        self.build_type_expr(child)
    }

    fn build_type_paren_group(&self, group: &Cst) -> Result<ActTypeExpr, ActTypeResolveError> {
        let children = group
            .children()
            .filter(|child| child.kind() == SyntaxKind::TypeExpr)
            .collect::<Vec<_>>();
        match children.as_slice() {
            [] => Ok(ActTypeExpr::Builtin(BuiltinType::Unit)),
            [child] => self.build_type_expr(child),
            _ => Err(ActTypeResolveError::UnsupportedSyntax { kind: group.kind() }),
        }
    }

    fn resolve_type_path(&self, path: Vec<Name>) -> Result<ActTypeExpr, ActTypeResolveError> {
        if let [name] = path.as_slice() {
            if let Some(builtin) = BuiltinType::from_surface_name(name.0.as_str()) {
                return Ok(ActTypeExpr::Builtin(builtin));
            }
            if let Some(decl) = self.modules.lexical_type_at(self.module, name, self.site) {
                return Ok(ActTypeExpr::Named(decl.id));
            }
            return Err(ActTypeResolveError::UnresolvedTypeName { path });
        }

        let Some((last, prefix)) = path.split_last() else {
            return Err(ActTypeResolveError::EmptyTypeExpr);
        };
        let Some(module) = self.resolve_module_prefix(prefix) else {
            return Err(ActTypeResolveError::UnresolvedTypeName { path });
        };
        let Some(decl) = self.modules.type_at(module, last, module_path_site()) else {
            return Err(ActTypeResolveError::UnresolvedTypeName { path });
        };
        Ok(ActTypeExpr::Named(decl.id))
    }

    fn resolve_module_prefix(&self, path: &[Name]) -> Option<ModuleId> {
        let (first, rest) = path.split_first()?;
        let mut current = self
            .modules
            .lexical_module_at(self.module, first, self.site)?;
        for segment in rest {
            current = self
                .modules
                .module_at(current, segment, module_path_site())?;
        }
        Some(current)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ResolvedActUse {
    pub decl: ModuleTypeDecl,
    pub args: Vec<ActTypeExpr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ActTypeExpr {
    Builtin(BuiltinType),
    Named(TypeDeclId),
    Var(String),
    Apply {
        callee: Box<ActTypeExpr>,
        args: Vec<ActTypeExpr>,
    },
    Function {
        param: Box<ActTypeExpr>,
        ret: Box<ActTypeExpr>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ActTypeResolveError {
    ExpectedTypeExpr { kind: SyntaxKind },
    EmptyTypeExpr,
    MissingFunctionReturn,
    UnresolvedTypeName { path: Vec<Name> },
    UnresolvedTypeId { id: TypeDeclId },
    InvalidActHead { ty: ActTypeExpr },
    UnsupportedSyntax { kind: SyntaxKind },
}

fn act_use_head(ty: ActTypeExpr) -> Option<(TypeDeclId, Vec<ActTypeExpr>)> {
    match ty {
        ActTypeExpr::Named(id) => Some((id, Vec::new())),
        ActTypeExpr::Apply { callee, args } => match *callee {
            ActTypeExpr::Named(id) => Some((id, args)),
            ActTypeExpr::Builtin(_)
            | ActTypeExpr::Var(_)
            | ActTypeExpr::Apply { .. }
            | ActTypeExpr::Function { .. } => None,
        },
        ActTypeExpr::Builtin(_) | ActTypeExpr::Var(_) | ActTypeExpr::Function { .. } => None,
    }
}

fn parse_type_path_prefix(items: &[CstItem]) -> Result<(Vec<Name>, usize), ActTypeResolveError> {
    let Some(NodeOrToken::Token(head)) = items.first() else {
        return Err(ActTypeResolveError::EmptyTypeExpr);
    };
    if head.kind() != SyntaxKind::Ident {
        return Err(ActTypeResolveError::UnsupportedSyntax { kind: head.kind() });
    }

    let mut segments = vec![Name(head.text().to_string())];
    let mut next = 1;
    for item in &items[1..] {
        let NodeOrToken::Node(path_sep) = item else {
            break;
        };
        if path_sep.kind() != SyntaxKind::PathSep {
            break;
        }

        let Some(segment) = path_sep
            .children_with_tokens()
            .filter_map(|item| item.into_token())
            .find(|token| token.kind() == SyntaxKind::Ident)
        else {
            return Err(ActTypeResolveError::UnsupportedSyntax {
                kind: path_sep.kind(),
            });
        };
        segments.push(Name(segment.text().to_string()));
        next += 1;
    }

    Ok((segments, next))
}

fn type_var_name(text: &str) -> String {
    text.trim_start_matches('\'').to_string()
}

fn module_path_site() -> ModuleOrder {
    ModuleOrder::from_index(u32::MAX)
}

fn item_is_trivia(item: &CstItem) -> bool {
    item.as_token().is_some_and(|token| {
        matches!(
            token.kind(),
            SyntaxKind::Space | SyntaxKind::LineComment | SyntaxKind::BlockComment
        )
    })
}
