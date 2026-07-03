use std::collections::HashSet;
use std::panic::{AssertUnwindSafe, catch_unwind};

use parser::lex::SyntaxKind;
use parser::op::{OpTable, standard_op_table};
use parser::sink::YulangLanguage;
use rowan::{NodeOrToken, SyntaxNode};

pub const TOKEN_TYPES: &[&str] = &[
    "function",      // 0
    "type",          // 1
    "typeParameter", // 2
    "namespace",     // 3
    "parameter",     // 4
    "keyword",       // 5
    "string",        // 6
    "number",        // 7
    "comment",       // 8
    "operator",      // 9
    "delimiter",     // 10
    "colon",         // 11
    "property",      // 12
    "pattern",       // 13
];

const FUNCTION: u32 = 0;
const TYPE: u32 = 1;
const TYPE_PARAMETER: u32 = 2;
const NAMESPACE: u32 = 3;
const PARAMETER: u32 = 4;
const KEYWORD: u32 = 5;
const STRING: u32 = 6;
const NUMBER: u32 = 7;
const COMMENT: u32 = 8;
const OPERATOR: u32 = 9;
const DELIMITER: u32 = 10;
const COLON: u32 = 11;
const PROPERTY: u32 = 12;
const PATTERN: u32 = 13;

pub fn compute(source: &str) -> Vec<u32> {
    compute_with_op_table(source, None)
}

pub fn compute_with_op_table(source: &str, op_table: Option<OpTable>) -> Vec<u32> {
    compute_with_op_table_and_highlights(source, op_table, None)
}

pub fn compute_with_op_table_and_highlights(
    source: &str,
    op_table: Option<OpTable>,
    highlights: Option<&ResolvedHighlightInfo>,
) -> Vec<u32> {
    let line_starts = compute_line_starts(source);
    let mut raw = stable_lexical_tokens(source, &line_starts);
    // Semantic token requests must stay total over edit fragments even when
    // parser recovery temporarily leaves the green builder unbalanced.
    let parsed = catch_unwind(AssertUnwindSafe(|| {
        parser::parse_module_to_green_with_ops(source, op_table.unwrap_or_else(standard_op_table))
    }));
    let green = match parsed {
        Ok(green) => green,
        Err(_) => {
            raw.extend(recovery_lexical_tokens(source, source, &line_starts, 0));
            raw.sort_unstable();
            raw.dedup();
            return encode(&raw);
        }
    };
    let root = SyntaxNode::<YulangLanguage>::new_root(green);
    compute_with_root_and_highlights_from_raw(source, &root, highlights, &line_starts, raw)
}

pub fn compute_with_root_and_highlights(
    source: &str,
    root: &SyntaxNode<YulangLanguage>,
    highlights: Option<&ResolvedHighlightInfo>,
) -> Vec<u32> {
    let line_starts = compute_line_starts(source);
    let raw = stable_lexical_tokens(source, &line_starts);
    compute_with_root_and_highlights_from_raw(source, root, highlights, &line_starts, raw)
}

fn compute_with_root_and_highlights_from_raw(
    source: &str,
    root: &SyntaxNode<YulangLanguage>,
    highlights: Option<&ResolvedHighlightInfo>,
    line_starts: &[usize],
    mut raw: Vec<(u32, u32, u32, u32)>,
) -> Vec<u32> {
    for node_or_token in root.descendants_with_tokens() {
        let token = match node_or_token {
            NodeOrToken::Token(t) => t,
            NodeOrToken::Node(_) => continue,
        };

        let kind = token.kind();
        let text = token.text();
        let start = usize::from(token.text_range().start());

        let classified = match kind {
            SyntaxKind::Number => Some((start, text.len(), NUMBER)),
            SyntaxKind::Sub => Some((start, text.len(), FUNCTION)),
            SyntaxKind::Do
            | SyntaxKind::If
            | SyntaxKind::Else
            | SyntaxKind::Elsif
            | SyntaxKind::Case
            | SyntaxKind::Catch
            | SyntaxKind::My
            | SyntaxKind::Our
            | SyntaxKind::Pub
            | SyntaxKind::Use
            | SyntaxKind::Type
            | SyntaxKind::Struct
            | SyntaxKind::Enum
            | SyntaxKind::Role
            | SyntaxKind::Impl
            | SyntaxKind::Act
            | SyntaxKind::Mod
            | SyntaxKind::As
            | SyntaxKind::For
            | SyntaxKind::In
            | SyntaxKind::With
            | SyntaxKind::Where
            | SyntaxKind::Via
            | SyntaxKind::Mark
            | SyntaxKind::Cast
            | SyntaxKind::Rule
            | SyntaxKind::Lazy => Some((start, text.len(), KEYWORD)),
            SyntaxKind::Arrow
            | SyntaxKind::Pipe
            | SyntaxKind::Backslash
            | SyntaxKind::DotDot
            | SyntaxKind::Tilde
            | SyntaxKind::RuleQuantStar
            | SyntaxKind::RuleQuantStarLazy
            | SyntaxKind::RuleQuantPlus
            | SyntaxKind::RuleQuantPlusLazy
            | SyntaxKind::RuleQuantOpt => Some((start, text.len(), OPERATOR)),
            SyntaxKind::Colon => Some((start, text.len(), COLON)),
            SyntaxKind::ColonColon => Some((start, text.len(), DELIMITER)),
            SyntaxKind::Equal => Some((start, text.len(), DELIMITER)),
            SyntaxKind::DocComment => Some((start, text.len(), COMMENT)),
            SyntaxKind::DotField => {
                // ".field" - highlight just the name after the dot.
                let name_start = start + 1;
                let name_len = text.len().saturating_sub(1);
                if name_len == 0 {
                    None
                } else {
                    Some((name_start, name_len, FUNCTION))
                }
            }
            SyntaxKind::Ident => classify_ident(&token, start, text.len(), highlights),
            SyntaxKind::SigilIdent => {
                // $foo / &foo - color only the sigil, not the variable name.
                Some((start, 1, OPERATOR))
            }
            // Registered operators: return, and, or, not, +, ==, etc.
            SyntaxKind::Prefix | SyntaxKind::Infix | SyntaxKind::Suffix | SyntaxKind::Nullfix => {
                Some((start, text.len(), OPERATOR))
            }
            _ => None,
        };

        if let Some((tok_start, tok_len, tok_type)) = classified {
            let (line, col) = byte_to_pos(source, &line_starts, tok_start);
            raw.push((line, col, utf16_len(text, tok_len), tok_type));
        } else if token
            .parent()
            .is_some_and(|parent| parent.kind() == SyntaxKind::InvalidToken)
        {
            raw.extend(recovery_lexical_tokens(source, text, line_starts, start));
        }
    }

    raw.sort_unstable();
    raw.dedup();
    encode(&raw)
}

#[derive(Debug, Clone, Default)]
pub struct ResolvedHighlightInfo {
    constructor_names: HashSet<String>,
    constructor_paths: HashSet<Vec<String>>,
}

impl ResolvedHighlightInfo {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert_constructor_name(&mut self, name: impl Into<String>) {
        self.constructor_names.insert(name.into());
    }

    pub fn insert_constructor_path<I, S>(&mut self, path: I)
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let segments = path.into_iter().map(Into::into).collect::<Vec<_>>();
        if let Some(last) = segments.last() {
            self.constructor_names.insert(last.clone());
        }
        self.constructor_paths.insert(segments);
    }

    fn is_constructor_name(&self, name: &str) -> bool {
        self.constructor_names.contains(name)
    }

    fn is_constructor_path(&self, path: &[String]) -> bool {
        self.constructor_paths.contains(path)
            || (path.len() == 1
                && path
                    .last()
                    .is_some_and(|name| self.constructor_names.contains(name)))
    }
}

fn stable_lexical_tokens(source: &str, line_starts: &[usize]) -> Vec<(u32, u32, u32, u32)> {
    let bytes = source.as_bytes();
    let mut tokens = Vec::new();
    let mut pos = 0;

    while pos < bytes.len() {
        match bytes[pos] {
            b'/' if bytes.get(pos + 1) == Some(&b'/') => {
                let start = pos;
                pos += 2;
                while pos < bytes.len() && bytes[pos] != b'\n' {
                    pos += 1;
                }
                push_source_token(source, line_starts, &mut tokens, start, pos, COMMENT);
            }
            b'/' if bytes.get(pos + 1) == Some(&b'*') => {
                let start = pos;
                pos += 2;
                while pos + 1 < bytes.len() {
                    if bytes[pos] == b'*' && bytes[pos + 1] == b'/' {
                        pos += 2;
                        break;
                    }
                    pos += 1;
                }
                push_source_token(source, line_starts, &mut tokens, start, pos, COMMENT);
            }
            b'"' => {
                let start = pos;
                pos += 1;
                while pos < bytes.len() {
                    match bytes[pos] {
                        b'\\' => pos = (pos + 2).min(bytes.len()),
                        b'"' => {
                            pos += 1;
                            break;
                        }
                        _ => pos += 1,
                    }
                }
                push_source_token(source, line_starts, &mut tokens, start, pos, STRING);
            }
            _ => pos += 1,
        }
    }

    tokens
}

fn recovery_lexical_tokens(
    full_source: &str,
    fragment: &str,
    line_starts: &[usize],
    base_offset: usize,
) -> Vec<(u32, u32, u32, u32)> {
    let bytes = fragment.as_bytes();
    let mut tokens = Vec::new();
    let mut pos = 0;

    while pos < bytes.len() {
        if bytes[pos].is_ascii_whitespace() {
            pos += 1;
            continue;
        }

        if bytes[pos] == b'/' && bytes.get(pos + 1) == Some(&b'/') {
            let start = pos;
            pos += 2;
            while pos < bytes.len() && bytes[pos] != b'\n' {
                pos += 1;
            }
            push_source_token(
                full_source,
                line_starts,
                &mut tokens,
                base_offset + start,
                base_offset + pos,
                COMMENT,
            );
            continue;
        }

        if bytes[pos] == b'/' && bytes.get(pos + 1) == Some(&b'*') {
            let start = pos;
            pos += 2;
            while pos + 1 < bytes.len() {
                if bytes[pos] == b'*' && bytes[pos + 1] == b'/' {
                    pos += 2;
                    break;
                }
                pos += 1;
            }
            push_source_token(
                full_source,
                line_starts,
                &mut tokens,
                base_offset + start,
                base_offset + pos,
                COMMENT,
            );
            continue;
        }

        if bytes[pos] == b'-' && bytes.get(pos + 1) == Some(&b'-') {
            let start = pos;
            pos += 2;
            while pos < bytes.len() && bytes[pos] != b'\n' {
                pos += 1;
            }
            push_source_token(
                full_source,
                line_starts,
                &mut tokens,
                base_offset + start,
                base_offset + pos,
                COMMENT,
            );
            continue;
        }

        if bytes[pos] == b'"' {
            let start = pos;
            pos = scan_string_end(bytes, pos + 1);
            push_source_token(
                full_source,
                line_starts,
                &mut tokens,
                base_offset + start,
                base_offset + pos,
                STRING,
            );
            continue;
        }

        if bytes[pos] == b'~' && bytes.get(pos + 1) == Some(&b'"') {
            let start = pos;
            pos = scan_string_end(bytes, pos + 2);
            push_source_token(
                full_source,
                line_starts,
                &mut tokens,
                base_offset + start,
                base_offset + pos,
                STRING,
            );
            continue;
        }

        if bytes[pos] == b'\'' && bytes.get(pos + 1).is_some_and(|b| is_ident_start(*b)) {
            let start = pos;
            pos += 2;
            while pos < bytes.len() && is_ident_continue(bytes[pos]) {
                pos += 1;
            }
            push_source_token(
                full_source,
                line_starts,
                &mut tokens,
                base_offset + start,
                base_offset + pos,
                TYPE_PARAMETER,
            );
            continue;
        }

        if bytes[pos].is_ascii_digit() {
            let start = pos;
            pos = scan_number_end(bytes, pos);
            push_source_token(
                full_source,
                line_starts,
                &mut tokens,
                base_offset + start,
                base_offset + pos,
                NUMBER,
            );
            continue;
        }

        if is_ident_start(bytes[pos]) {
            let start = pos;
            pos += 1;
            while pos < bytes.len() && is_ident_continue(bytes[pos]) {
                pos += 1;
            }
            let text = &fragment[start..pos];
            if let Some(token_type) = recovery_word_type(text) {
                push_source_token(
                    full_source,
                    line_starts,
                    &mut tokens,
                    base_offset + start,
                    base_offset + pos,
                    token_type,
                );
            } else if touches_path_separator(bytes, start, pos) {
                push_source_token(
                    full_source,
                    line_starts,
                    &mut tokens,
                    base_offset + start,
                    base_offset + pos,
                    NAMESPACE,
                );
            }
            continue;
        }

        if bytes[pos] == b':' && bytes.get(pos + 1) == Some(&b':') {
            push_source_token(
                full_source,
                line_starts,
                &mut tokens,
                base_offset + pos,
                base_offset + pos + 2,
                DELIMITER,
            );
            pos += 2;
            continue;
        }

        if bytes[pos] == b':' {
            push_source_token(
                full_source,
                line_starts,
                &mut tokens,
                base_offset + pos,
                base_offset + pos + 1,
                COLON,
            );
            pos += 1;
            continue;
        }

        if bytes[pos] == b'=' {
            push_source_token(
                full_source,
                line_starts,
                &mut tokens,
                base_offset + pos,
                base_offset + pos + 1,
                DELIMITER,
            );
            pos += 1;
            continue;
        }

        if matches!(
            bytes[pos],
            b'+' | b'-' | b'*' | b'/' | b'<' | b'>' | b'|' | b'\\'
        ) {
            let start = pos;
            pos += 1;
            while pos < bytes.len()
                && matches!(
                    bytes[pos],
                    b'+' | b'-' | b'*' | b'/' | b'<' | b'>' | b'|' | b'\\'
                )
            {
                pos += 1;
            }
            push_source_token(
                full_source,
                line_starts,
                &mut tokens,
                base_offset + start,
                base_offset + pos,
                OPERATOR,
            );
            continue;
        }

        pos += 1;
    }

    tokens
}

fn scan_string_end(bytes: &[u8], mut pos: usize) -> usize {
    while pos < bytes.len() {
        match bytes[pos] {
            b'\\' => pos = (pos + 2).min(bytes.len()),
            b'"' => {
                pos += 1;
                break;
            }
            _ => pos += 1,
        }
    }
    pos
}

fn scan_number_end(bytes: &[u8], mut pos: usize) -> usize {
    while pos < bytes.len() && (bytes[pos].is_ascii_digit() || bytes[pos] == b'_') {
        pos += 1;
    }
    if bytes.get(pos) == Some(&b'.') && bytes.get(pos + 1).is_some_and(u8::is_ascii_digit) {
        pos += 1;
        while pos < bytes.len() && (bytes[pos].is_ascii_digit() || bytes[pos] == b'_') {
            pos += 1;
        }
    }
    if matches!(bytes.get(pos), Some(b'e' | b'E')) {
        let exp = pos;
        pos += 1;
        if matches!(bytes.get(pos), Some(b'+' | b'-')) {
            pos += 1;
        }
        let digits = pos;
        while pos < bytes.len() && bytes[pos].is_ascii_digit() {
            pos += 1;
        }
        if digits == pos {
            pos = exp;
        }
    }
    pos
}

fn is_ident_start(byte: u8) -> bool {
    byte == b'_' || byte.is_ascii_alphabetic()
}

fn is_ident_continue(byte: u8) -> bool {
    byte == b'_' || byte.is_ascii_alphanumeric()
}

fn recovery_word_type(text: &str) -> Option<u32> {
    match text {
        "sub" => Some(FUNCTION),
        "do" | "if" | "else" | "elsif" | "case" | "catch" | "my" | "our" | "pub" | "use"
        | "type" | "struct" | "enum" | "error" | "role" | "impl" | "cast" | "act" | "mod"
        | "as" | "for" | "in" | "with" | "where" | "via" | "mark" | "rule" | "prefix" | "infix"
        | "suffix" | "nullfix" | "lazy" => Some(KEYWORD),
        _ => None,
    }
}

fn touches_path_separator(bytes: &[u8], start: usize, end: usize) -> bool {
    (start >= 2 && bytes.get(start - 2..start) == Some(b"::"))
        || bytes.get(end..end + 2) == Some(b"::")
}

fn push_source_token(
    source: &str,
    line_starts: &[usize],
    tokens: &mut Vec<(u32, u32, u32, u32)>,
    start: usize,
    end: usize,
    token_type: u32,
) {
    let (line, col) = byte_to_pos(source, line_starts, start);
    let len = source[start..end].encode_utf16().count() as u32;
    tokens.push((line, col, len, token_type));
}

fn classify_ident(
    token: &rowan::SyntaxToken<YulangLanguage>,
    start: usize,
    len: usize,
    highlights: Option<&ResolvedHighlightInfo>,
) -> Option<(usize, usize, u32)> {
    let parent = token.parent()?;
    let parent_kind = parent.kind();

    // Type variable list: 'a, 'b, ...
    if parent_kind == SyntaxKind::TypeVars || parent_kind == SyntaxKind::WherePredicate {
        return Some((start, len, TYPE_PARAMETER));
    }

    // Type expressions
    if is_type_expr(parent_kind) {
        return Some((start, len, TYPE));
    }

    if is_type_like_decl(parent_kind) && is_first_ident(token, &parent) {
        return Some((start, len, TYPE));
    }

    // Module path segments before ::  (PathSep node)
    if parent_kind == SyntaxKind::PathSep {
        if parent.parent().is_some_and(|gp| is_pattern_expr(gp.kind())) {
            if path_sep_continues(&parent) {
                return None;
            }
            return Some((start, len, TYPE));
        }

        if is_first_path_segment_before_sep(token) {
            return Some((start, len, NAMESPACE));
        }
        if path_sep_continues(&parent) {
            return None;
        }

        // Last segment in path - classify by grandparent context
        if let Some(gp) = parent.parent() {
            if is_type_expr(gp.kind()) {
                return Some((start, len, TYPE));
            }
            if highlights.is_some_and(|info| {
                path_sep_path(&parent).is_some_and(|path| info.is_constructor_path(&path))
            }) {
                return Some((start, len, TYPE));
            }
            if gp.kind() == SyntaxKind::Expr && path_tail_is_called(&parent) {
                return Some((start, len, FUNCTION));
            }
        }
        return None;
    }

    // Binding header: first Ident child = the name being defined
    // (in practice idents are always wrapped in Pattern; this path is a safety net)
    if parent_kind == SyntaxKind::BindingHeader {
        if is_first_ident(token, &parent) {
            if let Some(gp) = parent.parent() {
                return match gp.kind() {
                    SyntaxKind::TypeDecl
                    | SyntaxKind::StructDecl
                    | SyntaxKind::EnumDecl
                    | SyntaxKind::RoleDecl
                    | SyntaxKind::ImplDecl
                    | SyntaxKind::ActDecl
                    | SyntaxKind::CastDecl => Some((start, len, TYPE)),
                    _ => None,
                };
            }
        }
        return None;
    }

    // Struct field name definition - leave uncolored (plain text is fine here)
    if parent_kind == SyntaxKind::StructField {
        return None;
    }

    // Enum variant name
    if parent_kind == SyntaxKind::EnumVariant {
        if is_first_ident(token, &parent) {
            return Some((start, len, TYPE));
        }
    }

    // Ident inside a Pattern that is directly under BindingHeader
    if parent_kind == SyntaxKind::Pattern {
        if let Some(gp) = parent.parent() {
            if gp.kind() == SyntaxKind::BindingHeader {
                // First child Pattern = the binding name itself (not a param)
                let is_name =
                    first_child_node_of_kind(&gp, SyntaxKind::Pattern).as_ref() == Some(&parent);
                if is_name {
                    // Classify as function or variable (fall through to BindingHeader logic)
                    return classify_binding_name(token, &gp, start, len);
                } else {
                    return Some((start, len, PARAMETER));
                }
            }
        }
    }

    if is_pattern_expr(parent_kind) {
        if pattern_name_is_called(token)
            && highlights
                .map(|info| info.is_constructor_name(token.text()))
                .unwrap_or(true)
        {
            return Some((start, len, TYPE));
        }
        if token
            .siblings_with_tokens(rowan::Direction::Next)
            .skip(1)
            .find(|s| !is_trivia_kind(s.kind()))
            .is_some_and(|s| s.kind() == SyntaxKind::PathSep)
        {
            return None;
        }
        return Some((start, len, PATTERN));
    }

    // Function call: Ident in call position (parent is Expr, next non-trivia sibling is an apply node)
    if parent_kind == SyntaxKind::Expr {
        let next = token
            .siblings_with_tokens(rowan::Direction::Next)
            .skip(1)
            .find(|s| !is_trivia_kind(s.kind()));
        if let Some(next) = next {
            if next.kind() == SyntaxKind::ApplyColon && is_record_field_name_expr(&parent) {
                return Some((start, len, PROPERTY));
            }
            if matches!(
                next.kind(),
                SyntaxKind::ParenL
                    | SyntaxKind::ApplyC
                    | SyntaxKind::ApplyML
                    | SyntaxKind::ApplyColon
            ) {
                return Some((start, len, FUNCTION));
            }
        }
    }

    // Default: don't emit (let base theme color apply)
    None
}

fn pattern_name_is_called(token: &rowan::SyntaxToken<YulangLanguage>) -> bool {
    token
        .siblings_with_tokens(rowan::Direction::Next)
        .skip(1)
        .find(|s| !is_trivia_kind(s.kind()))
        .is_some_and(|s| matches!(s.kind(), SyntaxKind::ApplyC | SyntaxKind::ApplyML))
}

fn path_sep_continues(path_sep: &SyntaxNode<YulangLanguage>) -> bool {
    path_sep
        .siblings_with_tokens(rowan::Direction::Next)
        .skip(1)
        .find(|s| !is_trivia_kind(s.kind()))
        .is_some_and(|s| s.kind() == SyntaxKind::PathSep)
}

fn path_tail_is_called(path_sep: &SyntaxNode<YulangLanguage>) -> bool {
    path_sep
        .siblings_with_tokens(rowan::Direction::Next)
        .skip(1)
        .find(|s| !is_trivia_kind(s.kind()))
        .is_some_and(|s| {
            matches!(
                s.kind(),
                SyntaxKind::ApplyC | SyntaxKind::ApplyML | SyntaxKind::ApplyColon
            )
        })
}

fn is_first_path_segment_before_sep(token: &rowan::SyntaxToken<YulangLanguage>) -> bool {
    token
        .next_sibling_or_token()
        .is_some_and(|s| s.kind() == SyntaxKind::ColonColon)
        && token
            .parent()
            .is_none_or(|parent| parent.kind() != SyntaxKind::PathSep)
}

fn classify_binding_name(
    _token: &rowan::SyntaxToken<YulangLanguage>,
    binding_header: &SyntaxNode<YulangLanguage>,
    start: usize,
    len: usize,
) -> Option<(usize, usize, u32)> {
    // The name Pattern is the first child node of BindingHeader.
    let name_pattern = binding_header.children().next()?;

    // `our p.method = body`: Pattern contains a Field (dot-field) -> p is receiver, leave uncolored
    if name_pattern
        .children()
        .any(|c| c.kind() == SyntaxKind::Field)
    {
        return None;
    }

    // `my f(...) = body` / `my f x = body`: the name pattern contains an apply node.
    if name_pattern
        .descendants()
        .any(|c| matches!(c.kind(), SyntaxKind::ApplyML | SyntaxKind::ApplyC))
    {
        return Some((start, len, FUNCTION));
    }

    // `my y = ...`: plain variable binding, leave uncolored
    None
}

fn is_record_field_name_expr(expr: &SyntaxNode<YulangLanguage>) -> bool {
    let Some(brace) = expr
        .parent()
        .filter(|node| node.kind() == SyntaxKind::BraceGroup)
    else {
        return false;
    };
    is_record_literal_brace_group(&brace) && is_inline_record_field_expr(expr)
}

fn is_record_literal_brace_group(brace: &SyntaxNode<YulangLanguage>) -> bool {
    if brace.children().any(|child| {
        !matches!(child.kind(), SyntaxKind::Expr | SyntaxKind::Separator)
            && !(child.kind() == SyntaxKind::InvalidToken && child.to_string().contains(','))
    }) {
        return false;
    }

    let exprs = brace
        .children()
        .filter(|child| child.kind() == SyntaxKind::Expr)
        .collect::<Vec<_>>();
    if exprs.is_empty() {
        return true;
    }

    let has_colon = brace
        .descendants_with_tokens()
        .filter_map(|item| item.into_token())
        .any(|tok| tok.kind() == SyntaxKind::Colon);
    if !has_colon && !exprs.iter().any(is_record_spread_expr) {
        return false;
    }

    let mut field_exprs = exprs.as_slice();
    if let Some(first) = exprs.first() {
        if is_record_spread_expr(first) {
            field_exprs = &exprs[1..];
        }
    }
    if let Some(last) = field_exprs.last() {
        if is_record_spread_expr(last) {
            field_exprs = &field_exprs[..field_exprs.len().saturating_sub(1)];
        }
    }

    let mut i = 0;
    while i < field_exprs.len() {
        if is_inline_record_field_expr(&field_exprs[i]) {
            i += 1;
            continue;
        }
        if first_expr_ident_token(&field_exprs[i]).is_some() && field_exprs.get(i + 1).is_some() {
            i += 2;
            continue;
        }
        return false;
    }
    true
}

fn is_inline_record_field_expr(expr: &SyntaxNode<YulangLanguage>) -> bool {
    !expr
        .children()
        .any(|child| child.kind() == SyntaxKind::PathSep)
        && first_expr_ident_token(expr).is_some()
        && expr
            .children()
            .any(|child| child.kind() == SyntaxKind::ApplyColon)
}

fn is_record_spread_expr(expr: &SyntaxNode<YulangLanguage>) -> bool {
    expr.to_string().trim_start().starts_with("..")
}

fn first_expr_ident_token(
    expr: &SyntaxNode<YulangLanguage>,
) -> Option<rowan::SyntaxToken<YulangLanguage>> {
    expr.descendants_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| {
            matches!(
                t.kind(),
                SyntaxKind::Ident
                    | SyntaxKind::SigilIdent
                    | SyntaxKind::Prefix
                    | SyntaxKind::Infix
                    | SyntaxKind::Suffix
                    | SyntaxKind::Nullfix
            )
        })
}

fn path_sep_path(path_sep: &SyntaxNode<YulangLanguage>) -> Option<Vec<String>> {
    let parent = path_sep.parent()?;
    let mut segments = Vec::new();
    for item in parent.children_with_tokens() {
        match item {
            NodeOrToken::Token(token) if token.kind() == SyntaxKind::Ident => {
                segments.push(token.text().to_string());
            }
            NodeOrToken::Node(node) if node.kind() == SyntaxKind::PathSep => {
                if let Some(name) = node.children_with_tokens().find_map(|item| match item {
                    NodeOrToken::Token(token) if token.kind() == SyntaxKind::Ident => {
                        Some(token.text().to_string())
                    }
                    _ => None,
                }) {
                    segments.push(name);
                }
            }
            _ => {}
        }
    }
    (segments.len() >= 2).then_some(segments)
}

fn first_child_node_of_kind(
    node: &SyntaxNode<YulangLanguage>,
    kind: SyntaxKind,
) -> Option<SyntaxNode<YulangLanguage>> {
    node.children().find(|child| child.kind() == kind)
}

fn is_trivia_kind(kind: SyntaxKind) -> bool {
    // SyntaxKind values 0-99 are trivia (Space, LineComment, BlockComment*, etc.)
    (kind as u16) < 100
}

fn is_type_expr(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::TypeExpr
            | SyntaxKind::TypeApply
            | SyntaxKind::TypeCall
            | SyntaxKind::TypeArrow
            | SyntaxKind::TypeForall
            | SyntaxKind::TypeAnn
            | SyntaxKind::TypeRecord
            | SyntaxKind::TypeField
            | SyntaxKind::TypeRow
            | SyntaxKind::TypeParenGroup
            | SyntaxKind::TypePolyVariant
            | SyntaxKind::TypePolyVariantItem
    )
}

fn is_pattern_expr(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::Pattern
            | SyntaxKind::PatOr
            | SyntaxKind::PatAs
            | SyntaxKind::PatParenGroup
            | SyntaxKind::PatRecord
            | SyntaxKind::PatField
            | SyntaxKind::PatList
            | SyntaxKind::PatSpread
    )
}

fn is_type_like_decl(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::TypeDecl
            | SyntaxKind::StructDecl
            | SyntaxKind::EnumDecl
            | SyntaxKind::RoleDecl
            | SyntaxKind::ImplDecl
            | SyntaxKind::ActDecl
            | SyntaxKind::CastDecl
    )
}

fn is_first_ident(
    token: &rowan::SyntaxToken<YulangLanguage>,
    parent: &SyntaxNode<YulangLanguage>,
) -> bool {
    parent
        .children_with_tokens()
        .filter_map(|c| c.into_token())
        .filter(|t| t.kind() == SyntaxKind::Ident)
        .next()
        .is_some_and(|first| first == *token)
}

// -- encoding ------------------------------------------------------------------

fn compute_line_starts(text: &str) -> Vec<usize> {
    let mut starts = vec![0];
    for (i, c) in text.char_indices() {
        if c == '\n' {
            starts.push(i + 1);
        }
    }
    starts
}

fn byte_to_pos(source: &str, line_starts: &[usize], offset: usize) -> (u32, u32) {
    let line = line_starts
        .partition_point(|&s| s <= offset)
        .saturating_sub(1);
    let line_start = line_starts[line];
    let col = source[line_start..offset].encode_utf16().count();
    (line as u32, col as u32)
}

fn utf16_len(text: &str, byte_len: usize) -> u32 {
    text.get(..byte_len).unwrap_or(text).encode_utf16().count() as u32
}

/// Encode as the LSP delta format (5 u32s per token).
fn encode(tokens: &[(u32, u32, u32, u32)]) -> Vec<u32> {
    let mut out = Vec::with_capacity(tokens.len() * 5);
    let mut prev_line = 0u32;
    let mut prev_col = 0u32;

    for &(line, col, len, ty) in tokens {
        let delta_line = line - prev_line;
        let delta_col = if delta_line == 0 { col - prev_col } else { col };
        out.extend_from_slice(&[delta_line, delta_col, len, ty, 0]);
        prev_line = line;
        prev_col = col;
    }

    out
}

#[cfg(test)]
mod tests;
