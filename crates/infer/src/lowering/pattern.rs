//! lambda / case / catch arm に共通する pattern lowering。

use super::*;

impl<'a> ExprLowerer<'a> {
    pub(super) fn lower_lambda_pattern(
        &mut self,
        node: &Cst,
        value: TypeVar,
        local_effect: Option<LocalEffect>,
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
        local_effect: Option<LocalEffect>,
        call_return_effect: LocalCallReturnEffect,
    ) -> Result<PatId, LoweringError> {
        self.lower_pattern_with_ignored_tails(
            node,
            value,
            local_effect,
            call_return_effect,
            IgnoredPatternTails::default(),
        )
    }

    fn lower_pattern_with_ignored_tails(
        &mut self,
        node: &Cst,
        value: TypeVar,
        local_effect: Option<LocalEffect>,
        call_return_effect: LocalCallReturnEffect,
        ignored_tails: IgnoredPatternTails,
    ) -> Result<PatId, LoweringError> {
        if node.kind() == SyntaxKind::Pattern {
            if !ignored_tails.or
                && let Some(tail) = pattern_tail(node, SyntaxKind::PatOr)
            {
                return self.lower_or_pattern_tail(
                    node,
                    &tail,
                    value,
                    local_effect,
                    call_return_effect,
                    ignored_tails,
                );
            }
            if !ignored_tails.as_
                && let Some(tail) = pattern_tail(node, SyntaxKind::PatAs)
            {
                return self.lower_as_pattern_tail(
                    node,
                    &tail,
                    value,
                    local_effect,
                    call_return_effect,
                    ignored_tails,
                );
            }
        }
        if let Some(inner) = transparent_pattern_child(node) {
            return self.lower_pattern_with_ignored_tails(
                &inner,
                value,
                local_effect,
                call_return_effect,
                ignored_tails,
            );
        }
        match node.kind() {
            SyntaxKind::PatOr => {
                return self.lower_or_pattern(node, value, local_effect, call_return_effect);
            }
            SyntaxKind::PatAs => {
                return self.lower_as_pattern(node, value, local_effect, call_return_effect);
            }
            SyntaxKind::PatList => {
                return self.lower_list_pattern(node, value, local_effect, call_return_effect);
            }
            SyntaxKind::PatRecord => {
                return self.lower_record_pattern(node, value, local_effect, call_return_effect);
            }
            SyntaxKind::PatParenGroup => {
                return self.lower_paren_pattern(node, value, local_effect, call_return_effect);
            }
            _ => {}
        }

        if pattern_is_constructor_spine(node) {
            return self.lower_constructor_pattern(node, value, call_return_effect);
        }
        if let Some(name) = pattern_poly_variant_name(node) {
            return self.lower_poly_variant_pattern(
                name,
                node,
                value,
                local_effect,
                call_return_effect,
            );
        }

        match single_pattern_item_with_ignored_tails(node, ignored_tails)? {
            PatternItem::Ident(name) if name.0 == "_" => Ok(self.session.poly.add_pat(Pat::Wild)),
            PatternItem::Ident(name) => {
                Ok(self.bind_lambda_param(name, value, local_effect, call_return_effect))
            }
            PatternItem::Number(text) => self.lower_number_pattern(&text, value),
            PatternItem::String(text) => {
                self.constrain_exact_text_str(value);
                Ok(self.session.poly.add_pat(Pat::Lit(Lit::Str(text))))
            }
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
        local_effect: Option<LocalEffect>,
        call_return_effect: LocalCallReturnEffect,
    ) -> PatId {
        self.bind_pattern_local(name, value, local_effect, call_return_effect)
    }

    pub(super) fn bind_pattern_local(
        &mut self,
        name: Name,
        value: TypeVar,
        effect: Option<LocalEffect>,
        call_return_effect: LocalCallReturnEffect,
    ) -> PatId {
        let def = self.bind_pattern_local_def(name, value, effect, call_return_effect);
        self.session.poly.add_pat(Pat::Var(def))
    }

    fn bind_pattern_local_def(
        &mut self,
        name: Name,
        value: TypeVar,
        effect: Option<LocalEffect>,
        call_return_effect: LocalCallReturnEffect,
    ) -> DefId {
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
        def
    }

    fn lower_or_pattern(
        &mut self,
        node: &Cst,
        value: TypeVar,
        local_effect: Option<LocalEffect>,
        call_return_effect: LocalCallReturnEffect,
    ) -> Result<PatId, LoweringError> {
        let children = pattern_children(node);
        let [lhs, rhs] = children.as_slice() else {
            return Err(LoweringError::UnsupportedPatternSyntax { kind: node.kind() });
        };
        let lhs = self.lower_pattern(lhs, value, local_effect.clone(), call_return_effect)?;
        let rhs = self.lower_pattern(rhs, value, local_effect, call_return_effect)?;
        Ok(self.session.poly.add_pat(Pat::Or(lhs, rhs)))
    }

    fn lower_or_pattern_tail(
        &mut self,
        node: &Cst,
        tail: &Cst,
        value: TypeVar,
        local_effect: Option<LocalEffect>,
        call_return_effect: LocalCallReturnEffect,
        ignored_tails: IgnoredPatternTails,
    ) -> Result<PatId, LoweringError> {
        let rhs_node = pattern_children(tail)
            .into_iter()
            .next()
            .ok_or(LoweringError::UnsupportedPatternSyntax { kind: tail.kind() })?;
        let lhs = self.lower_pattern_with_ignored_tails(
            node,
            value,
            local_effect.clone(),
            call_return_effect,
            ignored_tails.with_or(),
        )?;
        let rhs = self.lower_pattern(&rhs_node, value, local_effect, call_return_effect)?;
        Ok(self.session.poly.add_pat(Pat::Or(lhs, rhs)))
    }

    fn lower_as_pattern(
        &mut self,
        node: &Cst,
        value: TypeVar,
        local_effect: Option<LocalEffect>,
        call_return_effect: LocalCallReturnEffect,
    ) -> Result<PatId, LoweringError> {
        let inner_node = pattern_children(node)
            .into_iter()
            .next()
            .ok_or(LoweringError::UnsupportedPatternSyntax { kind: node.kind() })?;
        let alias = pat_as_alias_name(node)
            .ok_or(LoweringError::UnsupportedPatternSyntax { kind: node.kind() })?;
        let inner =
            self.lower_pattern(&inner_node, value, local_effect.clone(), call_return_effect)?;
        let def = self.bind_pattern_local_def(alias, value, local_effect, call_return_effect);
        Ok(self.session.poly.add_pat(Pat::As(inner, def)))
    }

    fn lower_as_pattern_tail(
        &mut self,
        node: &Cst,
        tail: &Cst,
        value: TypeVar,
        local_effect: Option<LocalEffect>,
        call_return_effect: LocalCallReturnEffect,
        ignored_tails: IgnoredPatternTails,
    ) -> Result<PatId, LoweringError> {
        let alias = pat_as_alias_name(tail)
            .ok_or(LoweringError::UnsupportedPatternSyntax { kind: tail.kind() })?;
        let inner = self.lower_pattern_with_ignored_tails(
            node,
            value,
            local_effect.clone(),
            call_return_effect,
            ignored_tails.with_as(),
        )?;
        let def = self.bind_pattern_local_def(alias, value, local_effect, call_return_effect);
        Ok(self.session.poly.add_pat(Pat::As(inner, def)))
    }

    fn lower_list_pattern(
        &mut self,
        node: &Cst,
        value: TypeVar,
        _local_effect: Option<LocalEffect>,
        call_return_effect: LocalCallReturnEffect,
    ) -> Result<PatId, LoweringError> {
        let item = self.fresh_type_var();
        let list_path = self.builtin_op_con_path("list")?;
        self.constrain_list_value(value, item, &list_path);

        let mut prefix = Vec::new();
        let mut spread = None;
        let mut suffix = Vec::new();
        let mut after_spread = false;
        for child in node.children().filter(is_pattern_or_spread_node) {
            if child.kind() == SyntaxKind::PatSpread {
                if spread.is_none() {
                    let spread_node = child
                        .children()
                        .find(is_pattern_node)
                        .ok_or(LoweringError::UnsupportedPatternSyntax { kind: child.kind() })?;
                    let spread_value = self.fresh_type_var();
                    self.constrain_list_value(spread_value, item, &list_path);
                    spread = Some(self.lower_pattern(
                        &spread_node,
                        spread_value,
                        None,
                        call_return_effect,
                    )?);
                }
                after_spread = true;
                continue;
            }

            let pat = self.lower_pattern(&child, item, None, call_return_effect)?;
            if after_spread {
                suffix.push(pat);
            } else {
                prefix.push(pat);
            }
        }

        Ok(self.session.poly.add_pat(Pat::List {
            prefix,
            spread,
            suffix,
        }))
    }

    fn lower_record_pattern(
        &mut self,
        node: &Cst,
        value: TypeVar,
        local_effect: Option<LocalEffect>,
        call_return_effect: LocalCallReturnEffect,
    ) -> Result<PatId, LoweringError> {
        let mut fields = Vec::new();
        let mut pos_fields = Vec::new();
        let mut neg_fields = Vec::new();
        let mut spread = RecordSpread::None;
        let mut spread_tail = None;
        let mut saw_field = false;

        for child in node.children().filter(is_record_pattern_item_node) {
            match child.kind() {
                SyntaxKind::PatField => {
                    saw_field = true;
                    let field = self.lower_record_pattern_field(
                        &child,
                        local_effect.clone(),
                        call_return_effect,
                    )?;
                    pos_fields.push(RecordField {
                        name: field.name.clone(),
                        value: self.alloc_pos(Pos::Var(field.value)),
                        optional: field.optional,
                    });
                    neg_fields.push(RecordField {
                        name: field.name.clone(),
                        value: self.alloc_neg(Neg::Var(field.value)),
                        optional: field.optional,
                    });
                    fields.push((field.name, field.pat));
                }
                SyntaxKind::PatSpread => {
                    let (def, tail) = self.lower_record_pattern_spread(
                        &child,
                        local_effect.clone(),
                        call_return_effect,
                    )?;
                    spread = if saw_field {
                        RecordSpread::Tail(def)
                    } else {
                        RecordSpread::Head(def)
                    };
                    spread_tail = Some((saw_field, tail));
                }
                _ => {}
            }
        }

        let lower = if let Some((after_field, tail)) = spread_tail {
            let tail = self.alloc_pos(Pos::Var(tail));
            if after_field {
                Pos::RecordTailSpread {
                    fields: pos_fields.clone(),
                    tail,
                }
            } else {
                Pos::RecordHeadSpread {
                    tail,
                    fields: pos_fields.clone(),
                }
            }
        } else {
            Pos::Record(pos_fields)
        };
        self.constrain_lower(value, lower);
        self.constrain_upper(value, Neg::Record(neg_fields));
        Ok(self.session.poly.add_pat(Pat::Record { fields, spread }))
    }

    fn lower_poly_variant_pattern(
        &mut self,
        name: String,
        node: &Cst,
        value: TypeVar,
        local_effect: Option<LocalEffect>,
        call_return_effect: LocalCallReturnEffect,
    ) -> Result<PatId, LoweringError> {
        let payloads = pattern_payloads(node);
        let mut pats = Vec::with_capacity(payloads.len());
        let mut pos_payloads = Vec::with_capacity(payloads.len());
        let mut neg_payloads = Vec::with_capacity(payloads.len());
        for payload in payloads {
            let payload_value = self.fresh_type_var();
            pats.push(self.lower_pattern(
                &payload,
                payload_value,
                local_effect.clone(),
                call_return_effect,
            )?);
            pos_payloads.push(self.alloc_pos(Pos::Var(payload_value)));
            neg_payloads.push(self.alloc_neg(Neg::Var(payload_value)));
        }
        self.constrain_lower(value, Pos::PolyVariant(vec![(name.clone(), pos_payloads)]));
        self.constrain_upper(value, Neg::PolyVariant(vec![(name.clone(), neg_payloads)]));
        Ok(self.session.poly.add_pat(Pat::PolyVariant(name, pats)))
    }

    fn lower_record_pattern_field(
        &mut self,
        node: &Cst,
        local_effect: Option<LocalEffect>,
        call_return_effect: LocalCallReturnEffect,
    ) -> Result<LoweredRecordPatternField, LoweringError> {
        let name = pat_field_name(node).ok_or(LoweringError::MissingRecordFieldName)?;
        let value = self.fresh_type_var();
        let default = pat_field_default_expr(node)
            .map(|expr| self.lower_expr(&expr))
            .transpose()?;
        let optional = default.is_some();
        let pat = if let Some(pattern) = pat_field_pattern(node) {
            self.lower_pattern(&pattern, value, local_effect.clone(), call_return_effect)?
        } else {
            self.bind_pattern_local(
                name.clone(),
                value,
                local_effect.clone(),
                call_return_effect,
            )
        };
        if let Some(default) = default {
            self.subtype_var_to_var(default.value, value);
            self.subtype_var_to_var(value, default.value);
            if let Some(local_effect) = local_effect {
                self.subtype_var_to_local_effect(default.effect, &local_effect);
            }
        }
        Ok(LoweredRecordPatternField {
            name: name.0,
            value,
            pat,
            optional,
        })
    }

    fn lower_record_pattern_spread(
        &mut self,
        node: &Cst,
        local_effect: Option<LocalEffect>,
        call_return_effect: LocalCallReturnEffect,
    ) -> Result<(DefId, TypeVar), LoweringError> {
        let pattern = node
            .children()
            .find(is_pattern_node)
            .ok_or(LoweringError::UnsupportedPatternSyntax { kind: node.kind() })?;
        let value = self.fresh_type_var();
        let pat = self.lower_pattern(&pattern, value, local_effect, call_return_effect)?;
        match self.session.poly.pat(pat) {
            Pat::Var(def) => Ok((*def, value)),
            _ => Err(LoweringError::UnsupportedPatternSyntax { kind: node.kind() }),
        }
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

    fn constrain_exact_text_str(&mut self, value: TypeVar) {
        let path = crate::std_paths::text_str_type();
        self.constrain_lower(value, Pos::Con(path.clone(), Vec::new()));
        self.constrain_upper(value, Neg::Con(path, Vec::new()));
    }

    fn lower_paren_pattern(
        &mut self,
        group: &Cst,
        value: TypeVar,
        local_effect: Option<LocalEffect>,
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
    String(String),
    Paren(Cst),
    Unsupported(SyntaxKind),
}

struct LoweredRecordPatternField {
    name: String,
    value: TypeVar,
    pat: PatId,
    optional: bool,
}

pub(super) fn single_pattern_item(node: &Cst) -> Result<PatternItem, LoweringError> {
    single_pattern_item_with_ignored_tails(node, IgnoredPatternTails::default())
}

fn single_pattern_item_with_ignored_tails(
    node: &Cst,
    ignored_tails: IgnoredPatternTails,
) -> Result<PatternItem, LoweringError> {
    let items = node
        .children_with_tokens()
        .filter(|item| !item_is_trivia(item))
        .filter(|item| !ignored_pattern_item(item, ignored_tails))
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
        NodeOrToken::Node(child) if child.kind() == SyntaxKind::StringLit => {
            Ok(PatternItem::String(plain_string_lit_text(child)?))
        }
        NodeOrToken::Node(child) if child.kind() == SyntaxKind::RuleLit => {
            Ok(PatternItem::String(plain_rule_lit_text(child)?))
        }
        NodeOrToken::Node(child) if child.kind() == SyntaxKind::PatParenGroup => {
            Ok(PatternItem::Paren(child.clone()))
        }
        NodeOrToken::Node(child) => Ok(PatternItem::Unsupported(child.kind())),
    }
}

#[derive(Clone, Copy, Default)]
struct IgnoredPatternTails {
    or: bool,
    as_: bool,
}

impl IgnoredPatternTails {
    fn with_or(self) -> Self {
        Self { or: true, ..self }
    }

    fn with_as(self) -> Self {
        Self { as_: true, ..self }
    }
}

fn ignored_pattern_item(
    item: &NodeOrToken<Cst, rowan::SyntaxToken<YulangLanguage>>,
    ignored_tails: IgnoredPatternTails,
) -> bool {
    matches!(
        item,
        NodeOrToken::Node(child)
            if child.kind() == SyntaxKind::TypeAnn
                || ignored_tails.or && child.kind() == SyntaxKind::PatOr
                || ignored_tails.as_ && child.kind() == SyntaxKind::PatAs
    )
}

fn plain_rule_lit_text(node: &Cst) -> Result<String, LoweringError> {
    if node.children().any(|child| {
        matches!(
            child.kind(),
            SyntaxKind::RuleLazyCapture | SyntaxKind::RuleLitInterp
        )
    }) {
        return Err(LoweringError::UnsupportedSyntax {
            kind: SyntaxKind::RuleLit,
        });
    }

    let mut text = String::new();
    for token in node
        .children_with_tokens()
        .filter_map(|item| item.into_token())
    {
        if token.kind() == SyntaxKind::RuleLitText {
            text.push_str(token.text());
        }
    }
    Ok(text)
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
                            | SyntaxKind::PatList
                            | SyntaxKind::PatRecord
                    )
                })
                .collect::<Vec<_>>()
        })
        .collect()
}

fn transparent_pattern_child(node: &Cst) -> Option<Cst> {
    if node.kind() != SyntaxKind::Pattern {
        return None;
    }
    let child = pattern_children(node).into_iter().next()?;
    matches!(
        child.kind(),
        SyntaxKind::PatParenGroup | SyntaxKind::PatList | SyntaxKind::PatRecord
    )
    .then_some(child)
}

fn pattern_children(node: &Cst) -> Vec<Cst> {
    node.children().filter(is_pattern_node).collect()
}

fn pattern_tail(node: &Cst, kind: SyntaxKind) -> Option<Cst> {
    node.children().find(|child| child.kind() == kind)
}

fn is_pattern_or_spread_node(node: &Cst) -> bool {
    is_pattern_node(node) || node.kind() == SyntaxKind::PatSpread
}

fn is_record_pattern_item_node(node: &Cst) -> bool {
    matches!(node.kind(), SyntaxKind::PatField | SyntaxKind::PatSpread)
}

fn is_pattern_node(node: &Cst) -> bool {
    matches!(
        node.kind(),
        SyntaxKind::Pattern
            | SyntaxKind::PatOr
            | SyntaxKind::PatAs
            | SyntaxKind::PatParenGroup
            | SyntaxKind::PatList
            | SyntaxKind::PatRecord
    )
}

fn pat_field_name(node: &Cst) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::Ident)
        .map(|token| Name(token.text().to_string()))
}

fn pat_field_pattern(node: &Cst) -> Option<Cst> {
    node.children()
        .find(|child| child.kind() == SyntaxKind::Pattern)
}

fn pat_field_default_expr(node: &Cst) -> Option<Cst> {
    node.children()
        .find(|child| child.kind() == SyntaxKind::Expr)
}

fn pattern_poly_variant_name(node: &Cst) -> Option<String> {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::Symbol)
        .map(|token| token.text().trim_start_matches(':').to_string())
}

fn pat_as_alias_name(node: &Cst) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .filter(|token| matches!(token.kind(), SyntaxKind::Ident | SyntaxKind::SigilIdent))
        .last()
        .map(|token| Name(token.text().to_string()))
}

fn path_label(path: &[Name]) -> String {
    path.iter()
        .map(|name| name.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}
