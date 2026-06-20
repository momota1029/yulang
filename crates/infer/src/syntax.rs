use super::*;

// ── CST ヘルパ ───────────────────────────────────────────────────────────

pub(crate) fn child_node(node: &Cst, kind: SyntaxKind) -> Option<Cst> {
    node.children().find(|c| c.kind() == kind)
}

pub(crate) fn contains_node_kind(node: &Cst, kind: SyntaxKind) -> bool {
    node.children().any(|child| {
        child.kind() == kind
            || matches!(
                child.kind(),
                SyntaxKind::BindingHeader
                    | SyntaxKind::Pattern
                    | SyntaxKind::TypeAnn
                    | SyntaxKind::TypeExpr
                    | SyntaxKind::TypeApply
                    | SyntaxKind::TypeArrow
                    | SyntaxKind::TypeEffectRow
            ) && contains_node_kind(&child, kind)
    })
}

pub(crate) fn first_ident(node: &Cst) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| t.kind() == SyntaxKind::Ident)
        .map(|t| Name(t.text().to_string()))
}

pub(crate) fn first_ident_or_sigil(node: &Cst) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| matches!(t.kind(), SyntaxKind::Ident | SyntaxKind::SigilIdent))
        .map(|t| Name(t.text().to_string()))
}

pub(crate) fn node_source_range(node: &Cst) -> SourceRange {
    let range = node.text_range();
    SourceRange {
        start: usize::from(range.start()),
        end: usize::from(range.end()),
    }
}

pub(crate) fn source_range_for_name(node: &Cst, name: &Name) -> Option<SourceRange> {
    node.descendants_with_tokens()
        .filter_map(|item| item.into_token())
        .find_map(|token| token_source_range_for_name(&token, name))
}

fn token_source_range_for_name(
    token: &rowan::SyntaxToken<YulangLanguage>,
    name: &Name,
) -> Option<SourceRange> {
    match token.kind() {
        SyntaxKind::Ident | SyntaxKind::SigilIdent if token.text() == name.0 => {
            Some(token_source_range(token))
        }
        SyntaxKind::DotField if token.text().strip_prefix('.') == Some(name.0.as_str()) => {
            let range = token.text_range();
            Some(SourceRange {
                start: usize::from(range.start()) + 1,
                end: usize::from(range.end()),
            })
        }
        _ => None,
    }
}

pub(crate) fn token_source_range(token: &rowan::SyntaxToken<YulangLanguage>) -> SourceRange {
    let range = token.text_range();
    SourceRange {
        start: usize::from(range.start()),
        end: usize::from(range.end()),
    }
}

/// `Binding → BindingHeader → Pattern` から module value として登録する名前を読む。
pub(crate) fn binding_name(node: &Cst) -> Option<Name> {
    binding_value_names(node).into_iter().next()
}

pub(crate) fn binding_value_names(node: &Cst) -> Vec<Name> {
    let Some(header) = child_node(node, SyntaxKind::BindingHeader) else {
        return Vec::new();
    };
    let Some(pattern) = child_node(&header, SyntaxKind::Pattern) else {
        return Vec::new();
    };
    if contains_node_kind(&pattern, SyntaxKind::ApplyML)
        || contains_node_kind(&pattern, SyntaxKind::ApplyC)
        || contains_node_kind(&pattern, SyntaxKind::TypeAnn)
        || pattern_field_name(&pattern).is_some()
    {
        return pattern_head_binding_name(&pattern).into_iter().collect();
    }
    let mut out = Vec::new();
    collect_pattern_binding_names(&pattern, &mut out);
    out
}

pub(crate) fn binding_pattern(node: &Cst) -> Option<Cst> {
    let header = child_node(node, SyntaxKind::BindingHeader)?;
    child_node(&header, SyntaxKind::Pattern)
}

pub(crate) fn binding_has_single_head_pattern(node: &Cst) -> bool {
    let Some(pattern) = binding_pattern(node) else {
        return false;
    };
    pattern_head_binding_name(&pattern).is_some()
}

pub(crate) fn pattern_head_binding_name(pattern: &Cst) -> Option<Name> {
    match first_pattern_token_or_group(pattern)? {
        NodeOrToken::Token(token)
            if matches!(token.kind(), SyntaxKind::Ident | SyntaxKind::SigilIdent) =>
        {
            let name = Name(token.text().to_string());
            (name.0 != "_").then_some(name)
        }
        NodeOrToken::Node(group) if group.kind() == SyntaxKind::PatParenGroup => {
            pattern_head_binding_name(&single_pattern_child(&group)?)
        }
        _ => None,
    }
}

pub(crate) fn collect_pattern_binding_names(pattern: &Cst, out: &mut Vec<Name>) {
    if pattern.kind() == SyntaxKind::PatParenGroup {
        for child in pattern
            .children()
            .filter(|child| child.kind() == SyntaxKind::Pattern)
        {
            collect_pattern_binding_names(&child, out);
        }
        return;
    }

    let Some(item) = single_pattern_token_or_group(pattern) else {
        return;
    };
    match item {
        NodeOrToken::Token(token)
            if matches!(token.kind(), SyntaxKind::Ident | SyntaxKind::SigilIdent) =>
        {
            let name = Name(token.text().to_string());
            if name.0 != "_" {
                out.push(name);
            }
        }
        NodeOrToken::Node(group) if group.kind() == SyntaxKind::PatParenGroup => {
            collect_pattern_binding_names(&group, out);
        }
        _ => {}
    }
}

pub(crate) fn single_pattern_token_or_group(
    pattern: &Cst,
) -> Option<NodeOrToken<Cst, rowan::SyntaxToken<YulangLanguage>>> {
    let mut items = pattern
        .children_with_tokens()
        .filter(|item| !item_is_trivia(item));
    let first = items.next()?;
    items.next().is_none().then_some(first)
}

pub(crate) fn first_pattern_token_or_group(
    pattern: &Cst,
) -> Option<NodeOrToken<Cst, rowan::SyntaxToken<YulangLanguage>>> {
    pattern
        .children_with_tokens()
        .find(|item| !item_is_trivia(item))
}

pub(crate) fn single_pattern_child(group: &Cst) -> Option<Cst> {
    let mut patterns = group
        .children()
        .filter(|child| child.kind() == SyntaxKind::Pattern);
    let first = patterns.next()?;
    patterns.next().is_none().then_some(first)
}

pub(crate) fn binding_vis(node: &Cst) -> Vis {
    match child_node(node, SyntaxKind::BindingHeader) {
        Some(header) => vis_of(&header),
        None => Vis::Our,
    }
}

/// ModDecl の最初の Ident がモジュール名。
pub(crate) fn mod_name(node: &Cst) -> Option<Name> {
    first_ident(node)
}

/// 型名前空間に登録する宣言名。
pub(crate) fn type_decl_name(node: &Cst) -> Option<Name> {
    if node.kind() == SyntaxKind::RoleDecl {
        return child_node(node, SyntaxKind::TypeExpr)
            .and_then(|type_expr| first_ident(&type_expr));
    }
    first_ident(node)
}

#[derive(Debug, Clone)]
pub(crate) struct TypeMethodBindingInfo {
    pub(crate) name: Name,
    pub(crate) receiver: Name,
    pub(crate) receiver_kind: TypeMethodReceiver,
}

#[derive(Debug, Clone)]
pub(crate) struct RoleMethodBindingInfo {
    pub(crate) name: Name,
    pub(crate) receiver: Option<Name>,
}

pub(crate) fn type_method_binding(node: &Cst) -> Option<TypeMethodBindingInfo> {
    let header = child_node(node, SyntaxKind::BindingHeader)?;
    let pattern = child_node(&header, SyntaxKind::Pattern)?;
    let method = pattern_field_name(&pattern)?;
    let receiver = first_ident_or_sigil(&pattern)?;
    let receiver_kind = if receiver.0.starts_with('&') {
        TypeMethodReceiver::Ref
    } else {
        TypeMethodReceiver::Value
    };
    Some(TypeMethodBindingInfo {
        name: method,
        receiver,
        receiver_kind,
    })
}

pub(crate) fn role_method_binding(node: &Cst) -> Option<RoleMethodBindingInfo> {
    let header = child_node(node, SyntaxKind::BindingHeader)?;
    let pattern = child_node(&header, SyntaxKind::Pattern)?;
    let annotated = contains_node_kind(&pattern, SyntaxKind::TypeAnn);
    let receiver = first_ident_or_sigil(&pattern);
    let method = pattern_field_name(&pattern);
    match (method, receiver, annotated) {
        (Some(method), receiver, _) => Some(RoleMethodBindingInfo {
            name: method,
            receiver,
        }),
        (None, Some(name), true) => Some(RoleMethodBindingInfo {
            name,
            receiver: None,
        }),
        _ => None,
    }
}

pub(crate) fn role_impl_method_binding(node: &Cst) -> Option<RoleMethodBindingInfo> {
    role_method_binding(node).or_else(|| {
        if binding_vis(node) == Vis::My {
            return None;
        }
        Some(RoleMethodBindingInfo {
            name: binding_name(node)?,
            receiver: None,
        })
    })
}

pub(crate) fn binding_type_expr(binding: &Cst) -> Option<Cst> {
    let header = child_node(binding, SyntaxKind::BindingHeader)?;
    let pattern = child_node(&header, SyntaxKind::Pattern)?;
    direct_pattern_type_expr(&pattern)
}

pub(crate) fn binding_body_expr(binding: &Cst) -> Option<Cst> {
    let body = child_node(binding, SyntaxKind::BindingBody)?;
    body.children().find(|child| {
        matches!(
            child.kind(),
            SyntaxKind::Expr | SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
        )
    })
}

pub(crate) fn cast_pattern(cast: &Cst) -> Option<Cst> {
    child_node(cast, SyntaxKind::Pattern)
}

pub(crate) fn cast_source_type_expr(cast: &Cst) -> Option<Cst> {
    direct_pattern_type_expr(&cast_pattern(cast)?)
}

pub(crate) fn cast_target_type_expr(cast: &Cst) -> Option<Cst> {
    cast.children()
        .find(|child| child.kind() == SyntaxKind::TypeAnn)
        .and_then(|ann| {
            ann.children()
                .find(|child| child.kind() == SyntaxKind::TypeExpr)
        })
}

pub(crate) fn cast_body_expr(cast: &Cst) -> Option<Cst> {
    let body = child_node(cast, SyntaxKind::BindingBody)?;
    body.children().find(|child| {
        matches!(
            child.kind(),
            SyntaxKind::Expr | SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
        )
    })
}

pub(crate) fn local_var_act_name(binding: &Cst) -> Option<Name> {
    local_var_act_names(binding).into_iter().next()
}

pub(crate) fn local_var_act_names(binding: &Cst) -> Vec<Name> {
    let Some(pattern) = binding_pattern(binding) else {
        return Vec::new();
    };
    pattern_var_act_names(&pattern)
}

pub(crate) fn pattern_var_act_names(pattern: &Cst) -> Vec<Name> {
    let mut sources = Vec::new();
    collect_pattern_var_binding_sources(&pattern, &mut sources);
    sources
        .into_iter()
        .filter_map(|source| var_reference_name_from_source(&source))
        .collect()
}

pub(crate) fn collect_pattern_var_binding_sources(pattern: &Cst, out: &mut Vec<Name>) {
    let items = pattern
        .children_with_tokens()
        .filter(|item| !item_is_trivia(item))
        .collect::<Vec<_>>();
    if items.len() == 1 {
        collect_pattern_item_var_binding_sources(items[0].clone(), out);
        return;
    }
    for item in items {
        if let NodeOrToken::Node(group) = item {
            collect_pattern_group_var_binding_sources(&group, out);
        }
    }
}

fn collect_pattern_item_var_binding_sources(
    item: NodeOrToken<Cst, rowan::SyntaxToken<YulangLanguage>>,
    out: &mut Vec<Name>,
) {
    match item {
        NodeOrToken::Token(token) if token.kind() == SyntaxKind::SigilIdent => {
            let name = Name(token.text().to_string());
            if name.0.starts_with('$') {
                out.push(name);
            }
        }
        NodeOrToken::Node(group) if group.kind() == SyntaxKind::PatField => {
            collect_pat_field_var_binding_sources(&group, out);
        }
        NodeOrToken::Node(group) => collect_pattern_group_var_binding_sources(&group, out),
        _ => {}
    }
}

fn collect_pattern_group_var_binding_sources(group: &Cst, out: &mut Vec<Name>) {
    for child in group.children() {
        match child.kind() {
            SyntaxKind::Pattern => collect_pattern_var_binding_sources(&child, out),
            SyntaxKind::PatField => collect_pat_field_var_binding_sources(&child, out),
            _ => {}
        }
    }
}

fn collect_pat_field_var_binding_sources(field: &Cst, out: &mut Vec<Name>) {
    if let Some(pattern) = field
        .children()
        .find(|child| child.kind() == SyntaxKind::Pattern)
    {
        collect_pattern_var_binding_sources(&pattern, out);
        return;
    }

    if let Some(token) = field
        .children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::SigilIdent && token.text().starts_with('$'))
    {
        out.push(Name(token.text().to_string()));
    }
}

fn var_reference_name_from_source(source: &Name) -> Option<Name> {
    let raw = source.0.strip_prefix('$')?;
    (!raw.is_empty()).then(|| Name(format!("&{raw}")))
}

pub(crate) fn synthetic_var_act_internal_name(source: &Name, owner: DefId, index: usize) -> Name {
    Name(format!("{}#{}:{index}", source.0, owner.0))
}

pub(crate) fn synthetic_sub_label_act_internal_name(
    label: &Name,
    owner: DefId,
    index: usize,
) -> Name {
    let raw = label.0.trim_start_matches('\'');
    Name(format!("#sub_label:{raw}#{}:{index}", owner.0))
}

pub(crate) fn expr_needs_synthetic_owner(expr: &Cst) -> bool {
    expr.descendants().any(|node| {
        (node.kind() == SyntaxKind::Binding && local_var_act_name(&node).is_some())
            || (node.kind() == SyntaxKind::Pattern && !pattern_var_act_names(&node).is_empty())
            || sub_syntax_label(&node).is_some()
    })
}

pub(crate) struct SubSyntaxParts {
    pub label: Option<Name>,
    pub body: Cst,
}

pub(crate) struct SubLambdaSyntaxParts {
    pub label: Option<Name>,
    pub patterns: Vec<Cst>,
    pub body: Cst,
}

pub(crate) fn sub_syntax_parts(node: &Cst) -> Option<SubSyntaxParts> {
    match node.kind() {
        SyntaxKind::Expr => {
            let sub = node
                .children_with_tokens()
                .filter(|item| !item_is_trivia(item))
                .filter_map(|item| item.into_node())
                .find(|child| child.kind() == SyntaxKind::SubExpr)?;
            sub_expr_syntax_parts(&sub)
        }
        SyntaxKind::SubExpr => sub_expr_syntax_parts(node),
        _ => legacy_sub_syntax_parts(node),
    }
}

pub(crate) fn sub_expr_syntax_parts(node: &Cst) -> Option<SubSyntaxParts> {
    let label = sub_label_name(node);
    let body = sub_body_node(node)?;
    Some(SubSyntaxParts { label, body })
}

pub(crate) fn sub_lambda_syntax_parts(node: &Cst) -> Option<SubLambdaSyntaxParts> {
    let node = match node.kind() {
        SyntaxKind::Expr => node
            .children_with_tokens()
            .filter(|item| !item_is_trivia(item))
            .filter_map(|item| item.into_node())
            .find(|child| child.kind() == SyntaxKind::SubLambdaExpr)?,
        SyntaxKind::SubLambdaExpr => node.clone(),
        _ => return None,
    };
    let label = sub_label_name(&node);
    let patterns = node
        .children()
        .filter(|child| child.kind() == SyntaxKind::Pattern)
        .collect();
    let body = sub_body_node(&node)?;
    Some(SubLambdaSyntaxParts {
        label,
        patterns,
        body,
    })
}

pub(crate) fn legacy_sub_syntax_parts(node: &Cst) -> Option<SubSyntaxParts> {
    if node.kind() != SyntaxKind::Expr {
        return None;
    }
    let items = node
        .children_with_tokens()
        .filter(|item| !item_is_trivia(item))
        .collect::<Vec<_>>();
    let Some(NodeOrToken::Token(head)) = items.first() else {
        return None;
    };
    if head.kind() != SyntaxKind::Ident || head.text() != "sub" {
        return None;
    }

    let mut index = 1usize;
    let label = match items.get(index) {
        Some(NodeOrToken::Node(apply)) if apply.kind() == SyntaxKind::ApplyML => {
            let label = sub_syntax_label_arg_name(apply)?;
            index += 1;
            Some(label)
        }
        _ => None,
    };
    let Some(NodeOrToken::Node(colon)) = items.get(index) else {
        return None;
    };
    if colon.kind() != SyntaxKind::ApplyColon {
        return None;
    }
    let body = sub_syntax_body_from_apply_colon(colon)?;
    Some(SubSyntaxParts { label, body })
}

pub(crate) fn sub_syntax_label(node: &Cst) -> Option<Name> {
    sub_syntax_parts(node)
        .and_then(|parts| parts.label)
        .or_else(|| sub_lambda_syntax_parts(node).and_then(|parts| parts.label))
}

pub(crate) fn sub_label_name(node: &Cst) -> Option<Name> {
    child_node(node, SyntaxKind::SubLabel)?
        .children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::SigilIdent && token.text().starts_with('\''))
        .map(|token| Name(token.text().to_string()))
}

pub(crate) fn sub_body_node(node: &Cst) -> Option<Cst> {
    node.children().find(|child| {
        matches!(
            child.kind(),
            SyntaxKind::Expr | SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
        )
    })
}

pub(crate) fn sub_syntax_label_arg_name(node: &Cst) -> Option<Name> {
    let expr = node
        .children()
        .find(|child| child.kind() == SyntaxKind::Expr)?;
    expr.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::SigilIdent && token.text().starts_with('\''))
        .map(|token| Name(token.text().to_string()))
}

pub(crate) fn sub_syntax_body_from_apply_colon(node: &Cst) -> Option<Cst> {
    node.children().find(|child| {
        matches!(
            child.kind(),
            SyntaxKind::Expr | SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
        )
    })
}

pub(crate) fn direct_pattern_type_expr(pattern: &Cst) -> Option<Cst> {
    pattern
        .children()
        .find(|child| child.kind() == SyntaxKind::TypeAnn)
        .and_then(|ann| {
            ann.children()
                .find(|child| child.kind() == SyntaxKind::TypeExpr)
        })
}

pub(crate) fn pattern_field_name(pattern: &Cst) -> Option<Name> {
    pattern
        .children()
        .find(|child| child.kind() == SyntaxKind::Field)?
        .children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::DotField)
        .map(|token| Name(token.text().trim_start_matches('.').to_string()))
}

pub(crate) fn type_method_value_name(name: &Name, receiver: TypeMethodReceiver) -> Name {
    match receiver {
        TypeMethodReceiver::Value => name.clone(),
        TypeMethodReceiver::Ref => Name(format!("{}!", name.0)),
    }
}

pub(crate) fn act_method_value_name(name: &Name, def: DefId) -> Name {
    Name(format!("#act-method:{}:{}", name.0, def.0))
}

pub(crate) fn type_var_names(node: &Cst) -> Vec<String> {
    let Some(vars) = child_node(node, SyntaxKind::TypeVars) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for token in vars
        .children_with_tokens()
        .filter_map(|item| item.into_token())
    {
        if !matches!(token.kind(), SyntaxKind::Ident | SyntaxKind::SigilIdent) {
            continue;
        }
        let name = token.text().trim_start_matches('\'').to_string();
        if !out.contains(&name) {
            out.push(name);
        }
    }
    out
}

pub(crate) fn act_type_var_names(node: &Cst) -> Vec<String> {
    let mut out = Vec::new();
    let mut seen_act_name = false;
    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Token(token) if token.kind() == SyntaxKind::Ident && !seen_act_name => {
                seen_act_name = true;
            }
            NodeOrToken::Token(token)
                if seen_act_name && token.kind() == SyntaxKind::SigilIdent =>
            {
                let name = token.text().trim_start_matches('\'').to_string();
                if !out.contains(&name) {
                    out.push(name);
                }
            }
            NodeOrToken::Token(token)
                if matches!(
                    token.kind(),
                    SyntaxKind::Equal
                        | SyntaxKind::With
                        | SyntaxKind::Colon
                        | SyntaxKind::BraceL
                        | SyntaxKind::Semicolon
                ) =>
            {
                break;
            }
            NodeOrToken::Node(child)
                if matches!(
                    child.kind(),
                    SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
                ) =>
            {
                break;
            }
            NodeOrToken::Node(child) if seen_act_name && child.kind() == SyntaxKind::TypeExpr => {
                collect_act_type_param_names(&child, &mut out);
            }
            _ => {}
        }
    }
    out
}

pub(crate) fn collect_act_type_param_names(type_expr: &Cst, out: &mut Vec<String>) {
    if let Some(name) = bare_type_var_expr(type_expr) {
        push_unique_type_name(out, name);
    }
    for apply in type_expr
        .children()
        .filter(|child| child.kind() == SyntaxKind::TypeApply)
    {
        for arg in apply
            .children()
            .filter(|child| child.kind() == SyntaxKind::TypeExpr)
        {
            if let Some(name) = bare_type_var_expr(&arg) {
                push_unique_type_name(out, name);
            }
        }
    }
}

pub(crate) fn bare_type_var_expr(type_expr: &Cst) -> Option<String> {
    let items = type_expr
        .children_with_tokens()
        .filter(|item| !item_is_trivia(item))
        .filter(
            |item| !matches!(item, NodeOrToken::Node(node) if node.kind() == SyntaxKind::TypeApply),
        )
        .collect::<Vec<_>>();
    let [NodeOrToken::Token(token)] = items.as_slice() else {
        return None;
    };
    (token.kind() == SyntaxKind::SigilIdent)
        .then(|| token.text().trim_start_matches('\'').to_string())
}

pub(crate) fn push_unique_type_name(out: &mut Vec<String>, name: String) {
    if !out.contains(&name) {
        out.push(name);
    }
}

pub(crate) fn struct_field_nodes(node: &Cst) -> Vec<Cst> {
    let mut out = Vec::new();
    collect_pre_with_descendants(node, SyntaxKind::StructField, &mut out);
    out
}

pub(crate) fn struct_field_name(node: &Cst) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::Ident)
        .map(|token| Name(token.text().to_string()))
}

pub(crate) fn field_type_expr(node: &Cst) -> Option<Cst> {
    node.children()
        .find(|child| child.kind() == SyntaxKind::TypeExpr)
}

pub(crate) fn enum_variant_nodes(node: &Cst) -> Vec<Cst> {
    let mut out = Vec::new();
    collect_pre_with_descendants(node, SyntaxKind::EnumVariant, &mut out);
    out
}

pub(crate) fn enum_variant_name(node: &Cst) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::Ident)
        .map(|token| Name(token.text().to_string()))
}

pub(crate) fn enum_variant_field_nodes(node: &Cst) -> Vec<Cst> {
    node.descendants()
        .filter(|child| child.kind() == SyntaxKind::StructField)
        .collect()
}

pub(crate) fn enum_variant_direct_type_exprs(node: &Cst) -> Vec<Cst> {
    node.children()
        .filter(|child| child.kind() == SyntaxKind::TypeExpr)
        .collect()
}

pub(crate) fn enum_variant_has_from_marker(node: &Cst) -> bool {
    let mut seen_variant_name = false;
    for token in node
        .children_with_tokens()
        .filter_map(|item| item.into_token())
    {
        if token.kind() != SyntaxKind::Ident {
            continue;
        }
        if !seen_variant_name {
            seen_variant_name = true;
            continue;
        }
        return token.text() == "from";
    }
    false
}

pub(crate) fn collect_pre_with_descendants(node: &Cst, kind: SyntaxKind, out: &mut Vec<Cst>) {
    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Token(token) if token.kind() == SyntaxKind::With => break,
            NodeOrToken::Node(child) if child.kind() == kind => out.push(child),
            NodeOrToken::Node(child) => collect_pre_with_descendants(&child, kind, out),
            NodeOrToken::Token(_) => {}
        }
    }
}

pub(crate) fn role_input_names(node: &Cst) -> Vec<String> {
    let Some(type_expr) = child_node(node, SyntaxKind::TypeExpr) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for token in type_expr
        .descendants_with_tokens()
        .filter_map(|item| item.into_token())
    {
        if token.kind() != SyntaxKind::SigilIdent {
            continue;
        }
        let name = token.text().trim_start_matches('\'').to_string();
        if !out.contains(&name) {
            out.push(name);
        }
    }
    out
}

pub(crate) fn role_associated_names(node: &Cst) -> Vec<String> {
    role_decl_body(node)
        .into_iter()
        .flat_map(|body| body.children())
        .filter(|child| child.kind() == SyntaxKind::TypeDecl)
        .filter_map(|child| type_decl_name(&child))
        .map(|name| name.0)
        .collect()
}

pub(crate) fn type_with_body(node: &Cst) -> Option<Cst> {
    let mut seen_with = false;
    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Token(token) if token.kind() == SyntaxKind::With => {
                seen_with = true;
            }
            NodeOrToken::Node(child)
                if seen_with
                    && matches!(
                        child.kind(),
                        SyntaxKind::BraceGroup | SyntaxKind::IndentBlock
                    ) =>
            {
                return Some(child);
            }
            _ => {}
        }
    }
    None
}

pub(crate) fn type_self_struct_node(node: &Cst) -> Option<Cst> {
    type_with_body(node)?.children().find(|child| {
        child.kind() == SyntaxKind::StructDecl
            && type_decl_name(child).is_some_and(|name| name.0 == "self")
    })
}

pub(crate) fn role_decl_body(node: &Cst) -> Option<Cst> {
    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Node(child)
                if matches!(
                    child.kind(),
                    SyntaxKind::BraceGroup | SyntaxKind::IndentBlock
                ) =>
            {
                return Some(child);
            }
            _ => {}
        }
    }
    None
}

pub(crate) fn role_impl_body(node: &Cst) -> Option<Cst> {
    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Node(child)
                if matches!(
                    child.kind(),
                    SyntaxKind::BraceGroup | SyntaxKind::IndentBlock
                ) =>
            {
                return Some(child);
            }
            _ => {}
        }
    }
    None
}

pub(crate) fn act_decl_body(node: &Cst) -> Option<Cst> {
    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Node(child)
                if matches!(
                    child.kind(),
                    SyntaxKind::BraceGroup | SyntaxKind::IndentBlock
                ) =>
            {
                return Some(child);
            }
            _ => {}
        }
    }
    None
}

pub(crate) fn act_operation_binding(node: &Cst) -> bool {
    if type_method_binding(node).is_some() || child_node(node, SyntaxKind::BindingBody).is_some() {
        return false;
    }
    child_node(node, SyntaxKind::BindingHeader)
        .is_some_and(|header| contains_node_kind(&header, SyntaxKind::TypeAnn))
}

pub(crate) fn act_operation_signatures(node: &Cst) -> Vec<ActOperationSig> {
    act_decl_body(node)
        .into_iter()
        .flat_map(|body| act_operation_signatures_from_body(&body))
        .collect()
}

pub(crate) fn act_operation_signatures_from_body(body: &Cst) -> Vec<ActOperationSig> {
    body.children()
        .filter(|child| child.kind() == SyntaxKind::Binding && act_operation_binding(child))
        .filter_map(|binding| {
            Some(ActOperationSig {
                name: binding_name(&binding)?,
                signature: binding_type_expr(&binding),
            })
        })
        .collect()
}

pub(crate) fn act_copy_decl(node: &Cst) -> Option<ActCopyDecl> {
    let source = act_copy_source_type_expr(node)?;
    Some(ActCopyDecl { source })
}

pub(crate) fn act_copy_source_type_expr(node: &Cst) -> Option<Cst> {
    let mut after_equal = false;
    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Token(token) if token.kind() == SyntaxKind::Equal => {
                after_equal = true;
            }
            NodeOrToken::Node(child) if after_equal && child.kind() == SyntaxKind::TypeExpr => {
                return Some(child);
            }
            _ => {}
        }
    }
    None
}

pub(crate) fn act_type_var_arg_name(arg: &ActTypeExpr) -> Option<String> {
    match arg {
        ActTypeExpr::Var(name) => Some(name.clone()),
        ActTypeExpr::Builtin(_)
        | ActTypeExpr::Named(_)
        | ActTypeExpr::Apply { .. }
        | ActTypeExpr::Function { .. } => None,
    }
}

pub(crate) fn push_unique_act_ops(out: &mut Vec<ActOperationSig>, ops: Vec<ActOperationSig>) {
    for op in ops {
        if !out.iter().any(|existing| existing.name == op.name) {
            out.push(op);
        }
    }
}

pub(crate) fn item_is_trivia(item: &NodeOrToken<Cst, rowan::SyntaxToken<YulangLanguage>>) -> bool {
    item.as_token()
        .is_some_and(|token| matches!(token.kind(), SyntaxKind::Space | SyntaxKind::LineComment))
}

pub(crate) fn module_type_kind(kind: SyntaxKind) -> Option<ModuleTypeKind> {
    match kind {
        SyntaxKind::TypeDecl => Some(ModuleTypeKind::TypeAlias),
        SyntaxKind::StructDecl => Some(ModuleTypeKind::Struct),
        SyntaxKind::EnumDecl => Some(ModuleTypeKind::Enum),
        SyntaxKind::ErrorDecl => Some(ModuleTypeKind::Error),
        SyntaxKind::RoleDecl => Some(ModuleTypeKind::Role),
        SyntaxKind::ActDecl => Some(ModuleTypeKind::Act),
        _ => None,
    }
}

/// `use mod foo::...` の `foo`。
///
/// parser の設計では `use mod path` は `mod path_head; use path` の sugar なので、
/// pass1 でも先頭 module を module skeleton として登録する。
pub(crate) fn use_mod_name(node: &Cst) -> Option<Name> {
    let mut after_mod = false;
    for item in node.children_with_tokens() {
        let Some(token) = item.into_token() else {
            continue;
        };
        match token.kind() {
            SyntaxKind::Mod => after_mod = true,
            SyntaxKind::Ident if after_mod => return Some(Name(token.text().to_string())),
            _ => {}
        }
    }
    None
}

/// 直下の My/Our/Pub トークンを読む。無ければ Our（省略時の既定）。
pub(crate) const OP_FIXITY_TAGS: [&str; 4] = ["prefix", "infix", "suffix", "nullfix"];

/// op を value namespace に置くときの mangled 名。fixity 違いは別の値として共存する。
/// `#` 始まりは通常の識別子になり得ないため、ユーザ名と衝突しない。
pub(crate) fn op_value_name(fixity: &str, symbol: &str) -> Name {
    Name(format!("#op:{fixity}:{symbol}"))
}

pub(crate) struct OpDefInfo {
    pub(crate) name: Name,
    pub(crate) vis: Vis,
    pub(crate) lazy: bool,
    pub(crate) nullfix: bool,
    pub(crate) source_range: SourceRange,
}

/// OpDef ノードのヘッダから登録に要る情報を読む。bps は infer では使わない。
pub(crate) fn op_def_info(node: &Cst) -> Option<OpDefInfo> {
    let header = child_node(node, SyntaxKind::OpDefHeader)?;
    let symbol = header
        .children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|tok| tok.kind() == SyntaxKind::OpName)?;
    let source_range = token_source_range(&symbol);
    let symbol = symbol.text().to_string();
    let fixity = header
        .children_with_tokens()
        .filter_map(|item| item.into_token())
        .find_map(|tok| match tok.kind() {
            SyntaxKind::Prefix => Some("prefix"),
            SyntaxKind::Infix => Some("infix"),
            SyntaxKind::Suffix => Some("suffix"),
            SyntaxKind::Nullfix => Some("nullfix"),
            _ => None,
        })?;
    let lazy = header
        .children_with_tokens()
        .filter_map(|item| item.into_token())
        .any(|tok| tok.kind() == SyntaxKind::Lazy);
    Some(OpDefInfo {
        name: op_value_name(fixity, &symbol),
        vis: vis_of(&header),
        lazy,
        nullfix: fixity == "nullfix",
        source_range,
    })
}

pub(crate) fn vis_of(node: &Cst) -> Vis {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .find_map(|t| match t.kind() {
            SyntaxKind::Pub => Some(Vis::Pub),
            SyntaxKind::Our => Some(Vis::Our),
            SyntaxKind::My => Some(Vis::My),
            _ => None,
        })
        .unwrap_or(Vis::Our)
}
