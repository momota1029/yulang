use super::*;

pub fn build_ann_type_expr(
    modules: &ModuleTable,
    module: ModuleId,
    site: ModuleOrder,
    type_expr: &Cst,
) -> Result<AnnType, AnnBuildError> {
    AnnTypeBuilder::new(modules, module, site).build_type_expr(type_expr)
}

/// pass2 の annotation scope。
///
/// 1つの関数注釈で複数の `TypeExpr` を読む必要がある場合は、同じ builder を使い回す。
/// そうすると同名の surface type variable が同じ `AnnTypeVarId` を共有する。
pub struct AnnTypeBuilder<'a> {
    modules: &'a ModuleTable,
    module: ModuleId,
    site: ModuleOrder,
    self_alias: Option<AnnSelfAlias>,
    bare_type_vars: FxHashSet<String>,
    bare_type_var_aliases: FxHashMap<String, String>,
    type_aliases: FxHashMap<String, AnnType>,
    type_name_aliases: FxHashMap<String, TypeDeclId>,
    type_vars: FxHashMap<String, AnnTypeVarId>,
    next_type_var: u32,
}

impl<'a> AnnTypeBuilder<'a> {
    pub fn new(modules: &'a ModuleTable, module: ModuleId, site: ModuleOrder) -> Self {
        Self {
            modules,
            module,
            site,
            self_alias: None,
            bare_type_vars: FxHashSet::default(),
            bare_type_var_aliases: FxHashMap::default(),
            type_aliases: FxHashMap::default(),
            type_name_aliases: FxHashMap::default(),
            type_vars: FxHashMap::default(),
            next_type_var: 0,
        }
    }

    pub fn with_self_alias(
        modules: &'a ModuleTable,
        module: ModuleId,
        site: ModuleOrder,
        self_alias: AnnSelfAlias,
    ) -> Self {
        let mut builder = Self::new(modules, module, site);
        builder.self_alias = Some(self_alias);
        builder
    }

    pub fn set_self_alias(&mut self, self_alias: AnnSelfAlias) {
        self.self_alias = Some(self_alias);
    }

    pub fn add_bare_type_var(&mut self, name: impl Into<String>) {
        self.bare_type_vars.insert(name.into());
    }

    pub fn add_bare_type_var_alias(&mut self, alias: impl Into<String>, target: impl Into<String>) {
        self.bare_type_var_aliases
            .insert(alias.into(), target.into());
    }

    pub fn add_type_alias(&mut self, alias: impl Into<String>, target: AnnType) {
        self.type_aliases.insert(alias.into(), target);
    }

    pub fn add_type_name_alias(&mut self, alias: impl Into<String>, target: TypeDeclId) {
        self.type_name_aliases.insert(alias.into(), target);
    }

    pub fn ann_type_var_for_role(&mut self, name: &str) -> AnnTypeVar {
        self.ann_type_var(name)
    }

    pub fn type_var_bindings(&self) -> Vec<(String, AnnTypeVarId)> {
        self.type_vars
            .iter()
            .map(|(name, id)| (name.clone(), *id))
            .collect()
    }

    pub fn seed_type_var_bindings(&mut self, bindings: &[(String, AnnTypeVarId)]) {
        for (name, id) in bindings {
            self.type_vars.insert(name.clone(), *id);
            self.next_type_var = self.next_type_var.max(id.0.saturating_add(1));
        }
    }

    pub fn self_alias_type(&mut self) -> Option<AnnType> {
        let alias = self.self_alias.clone()?;
        Some(self.type_decl_application(alias.owner, &alias.type_vars))
    }

    pub fn type_decl_application(&mut self, owner: TypeDeclId, type_vars: &[String]) -> AnnType {
        let args = type_vars
            .iter()
            .map(|name| AnnType::Var(self.ann_type_var(name)))
            .collect::<Vec<_>>();
        if args.is_empty() {
            AnnType::Named(owner)
        } else {
            AnnType::Apply {
                callee: Box::new(AnnType::Named(owner)),
                args,
            }
        }
    }

    /// `TypeExpr` CST を、pass2 の scope で解決済み `AnnType` へ読む。
    pub fn build_type_expr(&mut self, type_expr: &Cst) -> Result<AnnType, AnnBuildError> {
        if type_expr.kind() != SyntaxKind::TypeExpr {
            return Err(AnnBuildError::ExpectedTypeExpr {
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
                .ok_or(AnnBuildError::MissingFunctionReturn)?;
            let (ret_eff, ret) = split_effectful_return(self.build_type_expr(&ret)?);
            return Ok(AnnType::Function {
                param: Box::new(param),
                arg_eff,
                ret_eff,
                ret: Box::new(ret),
            });
        }

        self.build_type_head(type_expr)
    }

    fn build_type_head(&mut self, type_expr: &Cst) -> Result<AnnType, AnnBuildError> {
        let items = type_expr
            .children_with_tokens()
            .filter(|item| !item_is_trivia(item))
            .filter(|item| {
                !matches!(item, NodeOrToken::Node(node) if node.kind() == SyntaxKind::TypeArrow)
            })
            .collect::<Vec<_>>();

        let Some(first) = items.first() else {
            return Err(AnnBuildError::EmptyTypeExpr);
        };

        if let NodeOrToken::Node(row) = first
            && row.kind() == SyntaxKind::TypeRow
        {
            let ret_items = &items[1..];
            let Some(ret_first) = ret_items.first() else {
                return Err(AnnBuildError::EmptyEffectfulType);
            };
            let (ret, next) = self.build_type_base(ret_items, ret_first)?;
            return Ok(AnnType::Effectful {
                eff: self.build_effect_row(row)?,
                ret: Box::new(self.build_type_applications(ret, &ret_items[next..])?),
            });
        }

        let (base, next) = self.build_type_base(&items, first)?;
        self.build_type_applications(base, &items[next..])
    }

    fn build_type_base(
        &mut self,
        items: &[CstItem],
        first: &CstItem,
    ) -> Result<(AnnType, usize), AnnBuildError> {
        match first {
            NodeOrToken::Token(token)
                if token.kind() == SyntaxKind::Ident && token.text() == "_" =>
            {
                Ok((AnnType::Wildcard(self.ann_wildcard_type()), 1))
            }
            NodeOrToken::Token(token) if token.kind() == SyntaxKind::Ident => {
                let (path, next) = parse_ann_path_prefix(items)?;
                Ok((self.resolve_ann_path(path)?, next))
            }
            NodeOrToken::Token(token) if token.kind() == SyntaxKind::SigilIdent => {
                Ok((AnnType::Var(self.ann_type_var(token.text())), 1))
            }
            NodeOrToken::Token(token) => {
                Err(AnnBuildError::UnsupportedSyntax { kind: token.kind() })
            }
            NodeOrToken::Node(node) if node.kind() == SyntaxKind::TypeParenGroup => {
                Ok((self.build_type_paren_group(node)?, 1))
            }
            NodeOrToken::Node(node) if node.kind() == SyntaxKind::TypeEffectRow => {
                Ok((AnnType::EffectRow(self.build_type_effect_row(node)?), 1))
            }
            NodeOrToken::Node(node) => Err(AnnBuildError::UnsupportedSyntax { kind: node.kind() }),
        }
    }

    fn build_type_applications(
        &mut self,
        base: AnnType,
        suffixes: &[CstItem],
    ) -> Result<AnnType, AnnBuildError> {
        let mut args = Vec::new();
        for item in suffixes {
            let NodeOrToken::Node(node) = item else {
                let kind = item
                    .as_token()
                    .map(|token| token.kind())
                    .unwrap_or(SyntaxKind::TypeExpr);
                return Err(AnnBuildError::UnsupportedSyntax { kind });
            };
            match node.kind() {
                SyntaxKind::TypeApply => {
                    args.push(self.build_single_type_arg(node)?);
                }
                SyntaxKind::TypeCall => {
                    let call_args = node
                        .children()
                        .filter(|child| child.kind() == SyntaxKind::TypeExpr)
                        .map(|child| self.build_type_expr(&child))
                        .collect::<Result<Vec<_>, _>>()?;
                    if call_args.is_empty() {
                        return Err(AnnBuildError::UnsupportedSyntax { kind: node.kind() });
                    }
                    args.extend(call_args);
                }
                _ => return Err(AnnBuildError::UnsupportedSyntax { kind: node.kind() }),
            }
        }

        if args.is_empty() {
            Ok(base)
        } else {
            Ok(AnnType::Apply {
                callee: Box::new(base),
                args,
            })
        }
    }

    fn build_single_type_arg(&mut self, apply: &Cst) -> Result<AnnType, AnnBuildError> {
        let children = apply
            .children()
            .filter(|child| child.kind() == SyntaxKind::TypeExpr)
            .collect::<Vec<_>>();
        let [child] = children.as_slice() else {
            return Err(AnnBuildError::UnsupportedSyntax { kind: apply.kind() });
        };
        self.build_type_expr(child)
    }

    fn build_type_paren_group(&mut self, group: &Cst) -> Result<AnnType, AnnBuildError> {
        let children = group
            .children()
            .filter(|child| child.kind() == SyntaxKind::TypeExpr)
            .collect::<Vec<_>>();
        match children.as_slice() {
            [] => Ok(AnnType::Builtin(BuiltinType::Unit)),
            [child] => self.build_type_expr(child),
            _ => children
                .iter()
                .map(|child| self.build_type_expr(child))
                .collect::<Result<Vec<_>, _>>()
                .map(AnnType::Tuple),
        }
    }

    fn build_type_effect_row(&mut self, effect_row: &Cst) -> Result<AnnEffectRow, AnnBuildError> {
        let row = effect_row
            .children()
            .find(|child| child.kind() == SyntaxKind::TypeRow)
            .ok_or(AnnBuildError::MissingEffectRow)?;
        self.build_effect_row(&row)
    }

    fn build_effect_row(&mut self, row: &Cst) -> Result<AnnEffectRow, AnnBuildError> {
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
                        items.push(AnnEffectAtom::Wildcard);
                        continue;
                    }
                    let ty = self.build_type_expr(&node)?;
                    if seen_tail_separator {
                        let AnnType::Var(var) = ty else {
                            return Err(AnnBuildError::InvalidEffectRowTail { ty });
                        };
                        tail = Some(var);
                    } else {
                        items.push(AnnEffectAtom::Type(ty));
                    }
                }
                NodeOrToken::Node(node)
                    if node.kind() == SyntaxKind::Separator && separator_has_semicolon(&node) =>
                {
                    seen_tail_separator = true;
                }
                NodeOrToken::Node(node) if node.kind() == SyntaxKind::Separator => {}
                NodeOrToken::Node(node) => {
                    return Err(AnnBuildError::UnsupportedSyntax { kind: node.kind() });
                }
                NodeOrToken::Token(token) => match token.kind() {
                    SyntaxKind::BracketL | SyntaxKind::BracketR | SyntaxKind::Comma => {}
                    SyntaxKind::Semicolon => seen_tail_separator = true,
                    kind => return Err(AnnBuildError::UnsupportedSyntax { kind }),
                },
            }
        }

        if !seen_tail_separator
            && tail.is_none()
            && items.len() == 1
            && let AnnEffectAtom::Type(AnnType::Var(var)) = &items[0]
        {
            return Ok(AnnEffectRow {
                items: Vec::new(),
                tail: Some(var.clone()),
            });
        }

        Ok(AnnEffectRow { items, tail })
    }

    fn resolve_ann_path(&mut self, path: Vec<Name>) -> Result<AnnType, AnnBuildError> {
        if let [name] = path.as_slice() {
            if name.0 == "self"
                && let Some(ty) = self.self_alias_type()
            {
                return Ok(ty);
            }
            if let Some(builtin) = BuiltinType::from_surface_name(name.0.as_str()) {
                return Ok(AnnType::Builtin(builtin));
            }
            if let Some(target) = self.bare_type_var_aliases.get(&name.0).cloned() {
                return Ok(AnnType::Var(self.ann_type_var(&target)));
            }
            if self.bare_type_vars.contains(&name.0) {
                return Ok(AnnType::Var(self.ann_type_var(&name.0)));
            }
            if let Some(target) = self.type_aliases.get(&name.0).cloned() {
                return Ok(target);
            }
            if let Some(target) = self.type_name_aliases.get(&name.0).copied() {
                return Ok(AnnType::Named(target));
            }
            if let Some(decl) = self.modules.lexical_type_at(self.module, name, self.site) {
                return Ok(AnnType::Named(decl.id));
            }
            return Err(AnnBuildError::UnresolvedTypeName { path });
        }

        let Some((last, prefix)) = path.split_last() else {
            return Err(AnnBuildError::EmptyTypeExpr);
        };
        let Some(module) = self.resolve_module_prefix(prefix) else {
            return Err(AnnBuildError::UnresolvedTypeName { path });
        };
        let Some(decl) = self.modules.type_at(module, last, module_path_site()) else {
            return Err(AnnBuildError::UnresolvedTypeName { path });
        };
        Ok(AnnType::Named(decl.id))
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

    fn ann_type_var(&mut self, text: &str) -> AnnTypeVar {
        let name = ann_type_var_name(text);
        let id = if let Some(id) = self.type_vars.get(&name) {
            *id
        } else {
            let id = AnnTypeVarId(self.next_type_var);
            self.next_type_var += 1;
            self.type_vars.insert(name.clone(), id);
            id
        };
        AnnTypeVar { id, name }
    }

    fn ann_wildcard_type(&mut self) -> AnnTypeVar {
        let id = AnnTypeVarId(self.next_type_var);
        self.next_type_var += 1;
        AnnTypeVar {
            id,
            name: format!("_{}", id.0),
        }
    }
}

fn split_effectful_return(ret: AnnType) -> (Option<AnnEffectRow>, AnnType) {
    match ret {
        AnnType::Effectful { eff, ret } => (Some(eff), *ret),
        ret => (None, ret),
    }
}

fn parse_ann_path_prefix(items: &[CstItem]) -> Result<(Vec<Name>, usize), AnnBuildError> {
    let Some(NodeOrToken::Token(head)) = items.first() else {
        return Err(AnnBuildError::EmptyTypeExpr);
    };
    if head.kind() != SyntaxKind::Ident {
        return Err(AnnBuildError::UnsupportedSyntax { kind: head.kind() });
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
            return Err(AnnBuildError::UnsupportedSyntax {
                kind: path_sep.kind(),
            });
        };
        segments.push(Name(segment.text().to_string()));
        next += 1;
    }

    Ok((segments, next))
}

fn ann_type_var_name(text: &str) -> String {
    text.trim_start_matches('\'').to_string()
}

pub(crate) fn args_from_ann(args: &[AnnType]) -> impl Iterator<Item = &AnnType> {
    args.iter()
}

pub(crate) fn effect_row_has_wildcard(row: &AnnEffectRow) -> bool {
    row.items
        .iter()
        .any(|atom| matches!(atom, AnnEffectAtom::Wildcard))
}

fn is_wildcard_type_expr(node: &Cst) -> bool {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .any(|token| token.kind() == SyntaxKind::Ident && token.text() == "_")
}

fn separator_has_semicolon(node: &Cst) -> bool {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .any(|token| token.kind() == SyntaxKind::Semicolon)
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
