//! Extracted lowering implementation.

use super::*;

pub(super) struct NegSignatureBuilder<'a> {
    modules: &'a ModuleTable,
    module: ModuleId,
    site: ModuleOrder,
    self_alias: Option<SignatureSelfAlias>,
}

impl<'a> NegSignatureBuilder<'a> {
    pub(super) fn with_self_alias(
        modules: &'a ModuleTable,
        module: ModuleId,
        site: ModuleOrder,
        self_alias: SignatureSelfAlias,
    ) -> Self {
        Self {
            modules,
            module,
            site,
            self_alias: Some(self_alias),
        }
    }

    pub(super) fn build_type_expr(
        &self,
        type_expr: &Cst,
    ) -> Result<NegSignature, NegSignatureBuildError> {
        self.build_signature_type_expr(type_expr)
            .map(NegSignature::new)
    }

    fn build_signature_type_expr(
        &self,
        type_expr: &Cst,
    ) -> Result<SignatureType, NegSignatureBuildError> {
        if type_expr.kind() != SyntaxKind::TypeExpr {
            return Err(NegSignatureBuildError::ExpectedTypeExpr {
                kind: type_expr.kind(),
            });
        }
        if let Some(arrow) = type_expr
            .children()
            .find(|child| child.kind() == SyntaxKind::TypeArrow)
        {
            let param = self.build_type_head(type_expr)?;
            let arg_eff = arrow
                .children()
                .find(|child| child.kind() == SyntaxKind::TypeRow)
                .map(|row| self.build_effect_row(&row))
                .transpose()?;
            let ret = arrow
                .children()
                .find(|child| child.kind() == SyntaxKind::TypeExpr)
                .ok_or(NegSignatureBuildError::MissingFunctionReturn)?;
            let (ret_eff, ret) = split_effectful_signature(self.build_signature_type_expr(&ret)?);
            return Ok(SignatureType::Function {
                param: Box::new(param),
                arg_eff,
                ret_eff,
                ret: Box::new(ret),
            });
        }

        self.build_type_head(type_expr)
    }

    fn build_type_head(&self, type_expr: &Cst) -> Result<SignatureType, NegSignatureBuildError> {
        let items = type_expr
            .children_with_tokens()
            .filter(|item| !item_is_trivia(item))
            .filter(|item| {
                !matches!(item, NodeOrToken::Node(node) if node.kind() == SyntaxKind::TypeArrow)
            })
            .collect::<Vec<_>>();

        let Some(first) = items.first() else {
            return Err(NegSignatureBuildError::EmptyTypeExpr);
        };

        if let NodeOrToken::Node(row) = first
            && row.kind() == SyntaxKind::TypeRow
        {
            let ret_items = &items[1..];
            let Some(ret_first) = ret_items.first() else {
                return Err(NegSignatureBuildError::EmptyEffectfulType);
            };
            let (ret, next) = self.build_type_base(ret_items, ret_first)?;
            return Ok(SignatureType::Effectful {
                eff: self.build_effect_row(row)?,
                ret: Box::new(self.build_type_applications(ret, &ret_items[next..])?),
            });
        }

        let (base, next) = self.build_type_base(&items, first)?;
        self.build_type_applications(base, &items[next..])
    }

    fn build_type_base(
        &self,
        items: &[CstItem],
        first: &CstItem,
    ) -> Result<(SignatureType, usize), NegSignatureBuildError> {
        match first {
            NodeOrToken::Token(token) if token.kind() == SyntaxKind::Ident => {
                let (path, next) = parse_signature_path_prefix(items)?;
                Ok((self.resolve_signature_path(path)?, next))
            }
            NodeOrToken::Token(token) if token.kind() == SyntaxKind::SigilIdent => {
                Ok((SignatureType::Var(signature_var(token.text())), 1))
            }
            NodeOrToken::Token(token) => {
                Err(NegSignatureBuildError::UnsupportedSyntax { kind: token.kind() })
            }
            NodeOrToken::Node(node) if node.kind() == SyntaxKind::TypeParenGroup => {
                Ok((self.build_type_paren_group(node)?, 1))
            }
            NodeOrToken::Node(node) if node.kind() == SyntaxKind::TypeEffectRow => Ok((
                SignatureType::EffectRow(self.build_type_effect_row(node)?),
                1,
            )),
            NodeOrToken::Node(node) => {
                Err(NegSignatureBuildError::UnsupportedSyntax { kind: node.kind() })
            }
        }
    }

    fn build_type_applications(
        &self,
        base: SignatureType,
        suffixes: &[CstItem],
    ) -> Result<SignatureType, NegSignatureBuildError> {
        let mut args = Vec::new();
        for item in suffixes {
            let NodeOrToken::Node(node) = item else {
                let kind = item
                    .as_token()
                    .map(|token| token.kind())
                    .unwrap_or(SyntaxKind::TypeExpr);
                return Err(NegSignatureBuildError::UnsupportedSyntax { kind });
            };
            match node.kind() {
                SyntaxKind::TypeApply => args.push(self.build_single_type_arg(node)?),
                SyntaxKind::TypeCall => {
                    let call_args = node
                        .children()
                        .filter(|child| child.kind() == SyntaxKind::TypeExpr)
                        .map(|child| self.build_signature_type_expr(&child))
                        .collect::<Result<Vec<_>, _>>()?;
                    if call_args.is_empty() {
                        return Err(NegSignatureBuildError::UnsupportedSyntax {
                            kind: node.kind(),
                        });
                    }
                    args.extend(call_args);
                }
                _ => {
                    return Err(NegSignatureBuildError::UnsupportedSyntax { kind: node.kind() });
                }
            }
        }

        if args.is_empty() {
            Ok(base)
        } else {
            Ok(SignatureType::Apply {
                callee: Box::new(base),
                args,
            })
        }
    }

    fn build_single_type_arg(&self, apply: &Cst) -> Result<SignatureType, NegSignatureBuildError> {
        let children = apply
            .children()
            .filter(|child| child.kind() == SyntaxKind::TypeExpr)
            .collect::<Vec<_>>();
        let [child] = children.as_slice() else {
            return Err(NegSignatureBuildError::UnsupportedSyntax { kind: apply.kind() });
        };
        self.build_signature_type_expr(child)
    }

    fn build_type_paren_group(&self, group: &Cst) -> Result<SignatureType, NegSignatureBuildError> {
        let children = group
            .children()
            .filter(|child| child.kind() == SyntaxKind::TypeExpr)
            .collect::<Vec<_>>();
        match children.as_slice() {
            [] => Ok(SignatureType::Builtin(BuiltinType::Unit)),
            [child] => self.build_signature_type_expr(child),
            _ => children
                .iter()
                .map(|child| self.build_signature_type_expr(child))
                .collect::<Result<Vec<_>, _>>()
                .map(SignatureType::Tuple),
        }
    }

    fn build_type_effect_row(
        &self,
        effect_row: &Cst,
    ) -> Result<SignatureEffectRow, NegSignatureBuildError> {
        let row = effect_row
            .children()
            .find(|child| child.kind() == SyntaxKind::TypeRow)
            .ok_or(NegSignatureBuildError::MissingEffectRow)?;
        self.build_effect_row(&row)
    }

    fn build_effect_row(&self, row: &Cst) -> Result<SignatureEffectRow, NegSignatureBuildError> {
        let mut items = Vec::new();
        let mut tail = None;
        let mut seen_tail_separator = false;

        for item in row
            .children_with_tokens()
            .filter(|item| !item_is_trivia(item))
        {
            match item {
                NodeOrToken::Node(node) if node.kind() == SyntaxKind::TypeExpr => {
                    if !seen_tail_separator && is_wildcard_type_expr(&node) {
                        items.push(SignatureEffectAtom::Wildcard);
                        continue;
                    }
                    let ty = self.build_signature_type_expr(&node)?;
                    if seen_tail_separator {
                        let SignatureType::Var(var) = ty else {
                            return Err(NegSignatureBuildError::InvalidEffectRowTail { ty });
                        };
                        tail = Some(var);
                    } else {
                        items.push(SignatureEffectAtom::Type(ty));
                    }
                }
                NodeOrToken::Node(node)
                    if node.kind() == SyntaxKind::Separator && separator_has_semicolon(&node) =>
                {
                    seen_tail_separator = true;
                }
                NodeOrToken::Node(node) if node.kind() == SyntaxKind::Separator => {}
                NodeOrToken::Node(node) => {
                    return Err(NegSignatureBuildError::UnsupportedSyntax { kind: node.kind() });
                }
                NodeOrToken::Token(token) => match token.kind() {
                    SyntaxKind::BracketL | SyntaxKind::BracketR | SyntaxKind::Comma => {}
                    SyntaxKind::Semicolon => seen_tail_separator = true,
                    kind => return Err(NegSignatureBuildError::UnsupportedSyntax { kind }),
                },
            }
        }

        if !seen_tail_separator
            && tail.is_none()
            && items.len() == 1
            && let SignatureEffectAtom::Type(SignatureType::Var(var)) = &items[0]
        {
            return Ok(SignatureEffectRow {
                items: Vec::new(),
                tail: Some(var.clone()),
            });
        }

        Ok(SignatureEffectRow { items, tail })
    }

    fn resolve_signature_path(
        &self,
        path: Vec<Name>,
    ) -> Result<SignatureType, NegSignatureBuildError> {
        if let [name] = path.as_slice() {
            if name.0 == "self"
                && let Some(ty) = self.self_alias_type()
            {
                return Ok(ty);
            }
            if let Some(builtin) = BuiltinType::from_surface_name(name.0.as_str()) {
                return Ok(SignatureType::Builtin(builtin));
            }
            if let Some(decl) = self.modules.lexical_type_at(self.module, name, self.site) {
                return Ok(SignatureType::Named(decl.id));
            }
            return Err(NegSignatureBuildError::UnresolvedTypeName { path });
        }

        let Some((last, prefix)) = path.split_last() else {
            return Err(NegSignatureBuildError::EmptyTypeExpr);
        };
        let Some(module) = self.resolve_module_prefix(prefix) else {
            return Err(NegSignatureBuildError::UnresolvedTypeName { path });
        };
        let Some(decl) = self
            .modules
            .type_at(module, last, signature_module_path_site())
        else {
            return Err(NegSignatureBuildError::UnresolvedTypeName { path });
        };
        Ok(SignatureType::Named(decl.id))
    }

    fn self_alias_type(&self) -> Option<SignatureType> {
        let alias = self.self_alias.as_ref()?;
        let args = alias
            .type_vars
            .iter()
            .map(|name| SignatureType::Var(SignatureVar { name: name.clone() }))
            .collect::<Vec<_>>();
        if args.is_empty() {
            Some(SignatureType::Named(alias.owner))
        } else {
            Some(SignatureType::Apply {
                callee: Box::new(SignatureType::Named(alias.owner)),
                args,
            })
        }
    }

    fn resolve_module_prefix(&self, path: &[Name]) -> Option<ModuleId> {
        let (first, rest) = path.split_first()?;
        let mut current = self
            .modules
            .lexical_module_at(self.module, first, self.site)?;
        for segment in rest {
            current = self
                .modules
                .module_at(current, segment, signature_module_path_site())?;
        }
        Some(current)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NegSignatureBuildError {
    ExpectedTypeExpr { kind: SyntaxKind },
    EmptyTypeExpr,
    EmptyEffectfulType,
    MissingFunctionReturn,
    MissingEffectRow,
    InvalidEffectRowTail { ty: SignatureType },
    UnresolvedTypeName { path: Vec<Name> },
    UnsupportedSyntax { kind: SyntaxKind },
}

fn parse_signature_path_prefix(
    items: &[CstItem],
) -> Result<(Vec<Name>, usize), NegSignatureBuildError> {
    let Some(NodeOrToken::Token(head)) = items.first() else {
        return Err(NegSignatureBuildError::EmptyTypeExpr);
    };
    if head.kind() != SyntaxKind::Ident {
        return Err(NegSignatureBuildError::UnsupportedSyntax { kind: head.kind() });
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
            return Err(NegSignatureBuildError::UnsupportedSyntax {
                kind: path_sep.kind(),
            });
        };
        segments.push(Name(segment.text().to_string()));
        next += 1;
    }

    Ok((segments, next))
}

fn signature_var(text: &str) -> SignatureVar {
    SignatureVar {
        name: text.trim_start_matches('\'').to_string(),
    }
}

fn is_wildcard_type_expr(node: &Cst) -> bool {
    let items = node
        .children_with_tokens()
        .filter(|item| !item_is_trivia(item))
        .collect::<Vec<_>>();
    let [NodeOrToken::Token(token)] = items.as_slice() else {
        return false;
    };
    token.kind() == SyntaxKind::Ident && token.text() == "_"
}

fn separator_has_semicolon(node: &Cst) -> bool {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .any(|token| token.kind() == SyntaxKind::Semicolon)
}

pub(super) fn signature_module_path_site() -> ModuleOrder {
    module_path_lookup_site()
}

pub(super) fn module_path_lookup_site() -> ModuleOrder {
    ModuleOrder::from_index(u32::MAX)
}

pub(super) struct ActCopyLoweringContext {
    pub(super) body: Cst,
    pub(super) type_var_aliases: Vec<(String, String)>,
    pub(super) type_name_aliases: Vec<(String, TypeDeclId)>,
}
