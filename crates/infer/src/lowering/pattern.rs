//! lambda / case / catch arm に共通する pattern lowering。

use super::*;

impl<'a> ExprLowerer<'a> {
    pub(super) fn lower_lambda_pattern(
        &mut self,
        node: &Cst,
        value: TypeVar,
        local_effect: Option<TypeVar>,
        call_return_effect: LocalCallReturnEffect,
    ) -> Result<PatId, LoweringError> {
        self.lower_pattern(node, value, local_effect, call_return_effect)
    }

    pub(super) fn lower_match_pattern(
        &mut self,
        node: &Cst,
        value: TypeVar,
    ) -> Result<PatId, LoweringError> {
        self.lower_pattern(node, value, None, LocalCallReturnEffect::Annotated)
    }

    fn lower_pattern(
        &mut self,
        node: &Cst,
        value: TypeVar,
        local_effect: Option<TypeVar>,
        call_return_effect: LocalCallReturnEffect,
    ) -> Result<PatId, LoweringError> {
        if pattern_is_constructor_spine(node) {
            return self.lower_constructor_pattern(node, value, call_return_effect);
        }

        match single_pattern_item(node)? {
            PatternItem::Ident(name) if name.0 == "_" => Ok(self.session.poly.add_pat(Pat::Wild)),
            PatternItem::Ident(name) => {
                Ok(self.bind_lambda_param(name, value, local_effect, call_return_effect))
            }
            PatternItem::Number(text) => self.lower_number_pattern(&text, value),
            PatternItem::Paren(group) => {
                self.lower_paren_pattern(&group, value, local_effect, call_return_effect)
            }
            PatternItem::Unsupported(kind) => Err(LoweringError::UnsupportedPatternSyntax { kind }),
        }
    }

    fn bind_lambda_param(
        &mut self,
        name: Name,
        value: TypeVar,
        local_effect: Option<TypeVar>,
        call_return_effect: LocalCallReturnEffect,
    ) -> PatId {
        self.bind_pattern_local(name, value, local_effect, call_return_effect)
    }

    pub(super) fn bind_pattern_local(
        &mut self,
        name: Name,
        value: TypeVar,
        effect: Option<TypeVar>,
        call_return_effect: LocalCallReturnEffect,
    ) -> PatId {
        let def = self.session.poly.defs.fresh();
        self.session.poly.defs.set(def, Def::Arg);
        if let Some(labels) = self.labels.as_mut() {
            labels.set_def_label(def, name.0.clone());
        }
        self.locals.push(LocalBinding {
            name,
            def,
            value,
            effect,
            call_return_effect,
            scheme: None,
        });
        self.session.poly.add_pat(Pat::Var(def))
    }

    fn lower_constructor_pattern(
        &mut self,
        node: &Cst,
        value: TypeVar,
        call_return_effect: LocalCallReturnEffect,
    ) -> Result<PatId, LoweringError> {
        let path = pattern_path(node)
            .ok_or(LoweringError::UnsupportedPatternSyntax { kind: node.kind() })?;
        let payloads = pattern_payloads(node);
        let constructor_value = self.fresh_type_var();
        let reference = self.lower_pattern_constructor_reference(&path, constructor_value);

        let mut payload_pats = Vec::with_capacity(payloads.len());
        let mut applied_value = constructor_value;
        for payload in payloads {
            let payload_value = self.fresh_type_var();
            payload_pats.push(self.lower_pattern(
                &payload,
                payload_value,
                None,
                call_return_effect,
            )?);
            let next_value = self.fresh_type_var();
            self.constrain_pattern_constructor_step(applied_value, payload_value, next_value);
            applied_value = next_value;
        }

        self.subtype_var_to_var(applied_value, value);
        self.subtype_var_to_var(value, applied_value);
        Ok(self.session.poly.add_pat(Pat::Con(reference, payload_pats)))
    }

    fn lower_pattern_constructor_reference(&mut self, path: &[Name], value: TypeVar) -> RefId {
        let reference = self.session.poly.add_ref();
        if let Some(labels) = self.labels.as_mut() {
            labels.set_ref_label(reference, path_label(path));
        }
        self.session.refs.insert(
            reference,
            RefUse {
                parent: self.parent,
                value,
            },
        );
        if let Some(target) = self.modules.value_path_at(self.module, path, self.site) {
            self.session.enqueue(AnalysisWork::ApplyRefResolution {
                ref_id: reference,
                target,
            });
        } else {
            self.session.enqueue(AnalysisWork::ResolveRef(reference));
        }
        reference
    }

    fn constrain_pattern_constructor_step(
        &mut self,
        constructor_value: TypeVar,
        payload_value: TypeVar,
        result_value: TypeVar,
    ) {
        let arg = self.alloc_pos(Pos::Var(payload_value));
        let arg_eff = self.alloc_pos(Pos::Bot);
        let ret_eff = self.empty_neg_row();
        let ret = self.alloc_neg(Neg::Var(result_value));
        self.constrain_upper(
            constructor_value,
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
        );
    }

    fn lower_number_pattern(&mut self, text: &str, value: TypeVar) -> Result<PatId, LoweringError> {
        let (lit, primitive) = parse_number_lit(text)?;
        self.constrain_exact_primitive(value, primitive);
        Ok(self.session.poly.add_pat(Pat::Lit(lit)))
    }

    fn lower_paren_pattern(
        &mut self,
        group: &Cst,
        value: TypeVar,
        local_effect: Option<TypeVar>,
        call_return_effect: LocalCallReturnEffect,
    ) -> Result<PatId, LoweringError> {
        let children = group
            .children()
            .filter(|child| child.kind() == SyntaxKind::Pattern)
            .collect::<Vec<_>>();
        match children.as_slice() {
            [] => {
                self.constrain_exact_primitive(value, "unit");
                Ok(self.session.poly.add_pat(Pat::Lit(Lit::Unit)))
            }
            [child] => self.lower_lambda_pattern(child, value, local_effect, call_return_effect),
            _ => {
                let mut pats = Vec::with_capacity(children.len());
                let mut pos_items = Vec::with_capacity(children.len());
                let mut neg_items = Vec::with_capacity(children.len());
                for child in children {
                    let item_value = self.fresh_type_var();
                    pats.push(self.lower_lambda_pattern(
                        &child,
                        item_value,
                        None,
                        LocalCallReturnEffect::Annotated,
                    )?);
                    pos_items.push(self.alloc_pos(Pos::Var(item_value)));
                    neg_items.push(self.alloc_neg(Neg::Var(item_value)));
                }
                self.constrain_lower(value, Pos::Tuple(pos_items));
                self.constrain_upper(value, Neg::Tuple(neg_items));
                Ok(self.session.poly.add_pat(Pat::Tuple(pats)))
            }
        }
    }
}

pub(super) enum PatternItem {
    Ident(Name),
    Number(String),
    Paren(Cst),
    Unsupported(SyntaxKind),
}

pub(super) fn single_pattern_item(node: &Cst) -> Result<PatternItem, LoweringError> {
    let items = node
        .children_with_tokens()
        .filter(|item| !item_is_trivia(item))
        .filter(
            |item| !matches!(item, NodeOrToken::Node(child) if child.kind() == SyntaxKind::TypeAnn),
        )
        .collect::<Vec<_>>();
    let Some(item) = items.first() else {
        return Err(LoweringError::UnsupportedPatternSyntax { kind: node.kind() });
    };
    if items.len() != 1 {
        return Ok(PatternItem::Unsupported(node.kind()));
    }

    match item {
        NodeOrToken::Token(token)
            if matches!(token.kind(), SyntaxKind::Ident | SyntaxKind::SigilIdent) =>
        {
            Ok(PatternItem::Ident(Name(token.text().to_string())))
        }
        NodeOrToken::Token(token) if token.kind() == SyntaxKind::Number => {
            Ok(PatternItem::Number(token.text().to_string()))
        }
        NodeOrToken::Token(token) => Ok(PatternItem::Unsupported(token.kind())),
        NodeOrToken::Node(child) if child.kind() == SyntaxKind::PatParenGroup => {
            Ok(PatternItem::Paren(child.clone()))
        }
        NodeOrToken::Node(child) => Ok(PatternItem::Unsupported(child.kind())),
    }
}

fn pattern_is_constructor_spine(node: &Cst) -> bool {
    let Some(path) = pattern_path(node) else {
        return false;
    };
    path.len() > 1 || !pattern_payloads(node).is_empty()
}

pub(super) fn pattern_path(node: &Cst) -> Option<Vec<Name>> {
    let mut names = Vec::new();
    for item in node
        .children_with_tokens()
        .filter(|item| !item_is_trivia(item))
    {
        match item {
            NodeOrToken::Token(token) if token.kind() == SyntaxKind::Ident => {
                if names.is_empty() {
                    names.push(Name(token.text().to_string()));
                }
            }
            NodeOrToken::Node(child) if child.kind() == SyntaxKind::PathSep => {
                if let Some(name) = path_sep_name(&child) {
                    names.push(name);
                }
            }
            _ => {}
        }
    }
    (!names.is_empty()).then_some(names)
}

fn path_sep_name(node: &Cst) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::Ident)
        .map(|token| Name(token.text().to_string()))
}

pub(super) fn pattern_payloads(node: &Cst) -> Vec<Cst> {
    node.children()
        .filter(|child| matches!(child.kind(), SyntaxKind::ApplyML | SyntaxKind::ApplyC))
        .flat_map(|apply| {
            apply
                .children()
                .filter(|child| {
                    matches!(
                        child.kind(),
                        SyntaxKind::Pattern
                            | SyntaxKind::PatOr
                            | SyntaxKind::PatAs
                            | SyntaxKind::PatParenGroup
                    )
                })
                .collect::<Vec<_>>()
        })
        .collect()
}

fn path_label(path: &[Name]) -> String {
    path.iter()
        .map(|name| name.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}
