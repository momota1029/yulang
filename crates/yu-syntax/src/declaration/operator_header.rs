//! Shared direct construction and fact projection for a dynamic operator header.

use std::{ops::Range, sync::Arc};

use reborrow_generic::Reborrow as _;

use crate::{
    BindingPower, BindingPowers, HeaderOperator, OperatorFixity, Visibility,
    lexical::operator_scan::OperatorSite,
    recovery_record::{
        DeclarationRole, ExpectationSources, ExpectedSyntax, GrammarRole, KeywordEvidence,
        OperatorHeaderRole, PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation,
        UnexpectedCategory, UnexpectedSyntax,
    },
    syntax_kind::SyntaxKind,
};

use crate::{
    cursor::recovery::{
        RecoveryDraft,
        emit::{emit_recovery_error_run, emit_recovery_missing, token_syntax_kind},
    },
    cursor::{LexIn, SyntaxIn},
    lexical::{
        current_item::{AcceptedPayload, CurrentItem, CurrentPayload, LineEntry, current_item},
        item::{Item, LeadingTrivia, Token, TokenKind},
        lexer::{scan_exact_equals, scan_operator_shaped_unknown},
        yumark::FenceBoundary,
    },
};

fn fixity(text: &str) -> Option<(OperatorFixity, SyntaxKind)> {
    Some(match text {
        "prefix" => (OperatorFixity::Prefix, SyntaxKind::PrefixKw),
        "infix" => (OperatorFixity::Infix, SyntaxKind::InfixKw),
        "suffix" => (OperatorFixity::Suffix, SyntaxKind::SuffixKw),
        "nullfix" => (OperatorFixity::Nullfix, SyntaxKind::NullfixKw),
        _ => return None,
    })
}

fn name(text: &str) -> Option<&str> {
    let inner = text.strip_prefix('(')?.strip_suffix(')')?;
    (!inner.is_empty()
        && inner.chars().all(|c| {
            !c.is_whitespace()
                && !matches!(
                    c,
                    '(' | ')' | '[' | ']' | '{' | '}' | '\\' | ',' | ';' | '"' | '\''
                )
        }))
    .then_some(inner)
}

fn power(text: &str) -> Option<BindingPower> {
    let components = text
        .split('.')
        .map(|part| {
            (!part.is_empty() && part.bytes().all(|c| c.is_ascii_digit()))
                .then(|| part.parse::<i8>().ok())
                .flatten()
        })
        .collect::<Option<Vec<_>>>()?;
    Some(BindingPower::from_components(components))
}

fn valid_power(text: &str) -> bool {
    text.split('.').all(|part| {
        !part.is_empty() && part.bytes().all(|c| c.is_ascii_digit()) && part.parse::<i8>().is_ok()
    })
}

fn power_shaped(text: &str) -> bool {
    text.split('.')
        .all(|part| !part.is_empty() && part.bytes().all(|c| c.is_ascii_digit()))
}

fn boundary(item: &Item) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || item.leading_view().contains_line_break()
        || matches!(
            item.payload_view().token_kind(),
            Some(
                TokenKind::Semicolon | TokenKind::RBrace | TokenKind::RBracket | TokenKind::RParen
            )
        )
}

fn accepts(item: &Item, role: OperatorHeaderRole) -> bool {
    let Some(text) = item.payload_view().spelling() else {
        return false;
    };
    match role {
        OperatorHeaderRole::Fixity => fixity(text).is_some(),
        OperatorHeaderRole::Name => name(text).is_some(),
        OperatorHeaderRole::LeftBindingPower | OperatorHeaderRole::RightBindingPower => {
            valid_power(text) && !item.leading_view().is_grammar_empty()
        }
        OperatorHeaderRole::DefinitionIntroducer => text == "=",
    }
}

fn safe_point(item: &Item, role: OperatorHeaderRole) -> bool {
    let text = item.payload_view().spelling().unwrap_or("");
    match role {
        OperatorHeaderRole::Name => valid_power(text) || text == "=",
        OperatorHeaderRole::LeftBindingPower | OperatorHeaderRole::RightBindingPower => {
            text == "=" || (!power_shaped(text) && crate::expression::is_nud_item(item))
        }
        OperatorHeaderRole::DefinitionIntroducer => crate::expression::is_nud_item(item),
        OperatorHeaderRole::Fixity => false,
    }
}

fn draft(
    role: OperatorHeaderRole,
    kind: RecoveryKind,
    range: Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let expected: Vec<_> = match role {
        OperatorHeaderRole::Fixity => [
            KeywordEvidence::Prefix,
            KeywordEvidence::Infix,
            KeywordEvidence::Suffix,
            KeywordEvidence::Nullfix,
        ]
        .into_iter()
        .map(ExpectedSyntax::Keyword)
        .collect(),
        OperatorHeaderRole::Name => vec![ExpectedSyntax::OperatorName],
        OperatorHeaderRole::DefinitionIntroducer => {
            vec![ExpectedSyntax::Punctuation(PunctuationEvidence::Equals)]
        }
        _ => vec![ExpectedSyntax::BindingPower],
    };
    let role = GrammarRole::Declaration(DeclarationRole::OperatorHeader(role));
    RecoveryDraft::new(
        RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        expected
            .into_iter()
            .map(|expected| SyntaxExpectation {
                role,
                expected,
                range: range.clone(),
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            })
            .collect::<Vec<_>>()
            .into(),
        0,
    )
}

/// Acquire an Item once, retaining the coordinate immediately after its payload.
pub(crate) fn next_item(
    i: LexIn,
    origin: usize,
    line: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    next_slot_item(i, origin, line, fence, true)
}

fn next_slot_item(
    mut i: LexIn,
    origin: usize,
    line: LineEntry,
    fence: Option<&FenceBoundary>,
    operator_name: bool,
) -> (Item, usize, LineEntry) {
    let before = i.remainder().len();
    let CurrentItem {
        item,
        next_line_entry,
    } = current_item(
        i.rb(),
        origin,
        line,
        fence,
        |mut lex, gap, payload_origin, _, _| {
            let special = lex.token(|mut lex| {
                let (accepted, text) = lex.rb().with_str(|mut lex| {
                    let first = lex.remainder().chars().next()?;
                    if first == '(' && operator_name {
                        lex.next()?;
                        while let Some(c) = lex.remainder().chars().next() {
                            if c == ')' {
                                lex.next()?;
                                return Some(());
                            }
                            if c.is_whitespace()
                                || matches!(
                                    c,
                                    '(' | '[' | ']' | '{' | '}' | '\\' | ',' | ';' | '"' | '\''
                                )
                            {
                                return None;
                            }
                            lex.next()?;
                        }
                        None
                    } else if first.is_ascii_digit() {
                        while lex
                            .remainder()
                            .chars()
                            .next()
                            .is_some_and(|c| c.is_ascii_digit() || c == '.')
                        {
                            lex.next()?;
                        }
                        Some(())
                    } else {
                        None
                    }
                });
                accepted?;
                Some(Token {
                    kind: if text.starts_with('(') {
                        TokenKind::Identifier
                    } else {
                        TokenKind::Integer
                    },
                    text: text.into(),
                })
            });
            if let Some(token) = special
                .or_else(|| lex.token(scan_exact_equals))
                .or_else(|| {
                    lex.remainder()
                        .starts_with('=')
                        .then(|| lex.token(scan_operator_shaped_unknown))
                        .flatten()
                })
            {
                return Some(AcceptedPayload {
                    payload: CurrentPayload::Token(token),
                    next_line_entry: LineEntry::InLine,
                });
            }
            crate::lexical::expression_item::scan_expression_payload_with_literals(
                lex,
                OperatorSite::Nud,
                gap,
                payload_origin,
                fence,
                0,
                0,
            )
        },
    )
    .expect("operator header scanning is total");
    (item, origin + before - i.remainder().len(), next_line_entry)
}

fn required(
    i: SyntaxIn,
    mut item: Item,
    mut origin: usize,
    mut line: LineEntry,
    fence: Option<&FenceBoundary>,
    role: OperatorHeaderRole,
) -> (Item, usize, LineEntry, bool) {
    if boundary(&item) || (!accepts(&item, role) && safe_point(&item, role)) {
        let at = item.payload_view().pending_boundary().map_or_else(
            || item.extent(origin).recovery_range().start,
            |boundary| boundary.coordinate(),
        );
        emit_recovery_missing(i, LeadingTrivia::default(), at, |range| {
            draft(role, RecoveryKind::Missing, range, Arc::from([]))
        });
        return (item, origin, line, false);
    }
    if accepts(&item, role) {
        return (item, origin, line, true);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    emit_recovery_error_run(
        i,
        |run| {
            let start = item.extent(origin).recovery_range().start;
            loop {
                let kind = item
                    .payload_view()
                    .token_kind()
                    .map(token_syntax_kind)
                    .unwrap_or(SyntaxKind::Operator);
                let extent = run.emit_item_as(item, origin, kind);
                (item, origin, line) = run.lexical(|lex| {
                    next_slot_item(lex, origin, line, fence, role == OperatorHeaderRole::Name)
                });
                if boundary(&item) || accepts(&item, role) || safe_point(&item, role) {
                    run.append_unexpected(UnexpectedSyntax::Token {
                        range: start..extent.recovery_range().end,
                        category: UnexpectedCategory::OtherCharacter,
                    });
                    let admitted = !boundary(&item) && accepts(&item, role);
                    return (item, origin, line, admitted);
                }
            }
        },
        |range, unexpected| draft(role, RecoveryKind::Error, range, unexpected),
    )
}

/// The intro has already been selected by the caller. A fact is published only
/// after the actual equals token; expression-body completion is independent.
pub(crate) fn operator_header_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    mut origin: usize,
    mut line: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Option<Item>, usize, LineEntry, Option<HeaderOperator>) {
    let start = item.extent(origin).recovery_range().end
        - item
            .payload_view()
            .spelling()
            .expect("selected header intro")
            .len();
    i.state.start_node(SyntaxKind::OperatorHeader.into());
    let mut visibility = Visibility::Private;
    if let Some((value, kind)) = match item.payload_view().spelling() {
        Some("my") => Some((Visibility::Private, SyntaxKind::MyKw)),
        Some("our") => Some((Visibility::Our, SyntaxKind::OurKw)),
        Some("pub") => Some((Visibility::Public, SyntaxKind::PubKw)),
        _ => None,
    } {
        visibility = value;
        item.emit_remaining(&mut *i.state, kind);
        (item, origin, line) = i
            .token(|lex| Some(next_item(lex, origin, line, fence)))
            .unwrap();
    }
    let lazy = item.payload_view().spelling() == Some("lazy");
    if lazy {
        item.emit_remaining(&mut *i.state, SyntaxKind::LazyKw);
        (item, origin, line) = i
            .token(|lex| Some(next_item(lex, origin, line, fence)))
            .unwrap();
    }
    let (next, next_origin, next_line, admitted) = required(
        i.rb(),
        item,
        origin,
        line,
        fence,
        OperatorHeaderRole::Fixity,
    );
    (item, origin, line) = (next, next_origin, next_line);
    if !admitted {
        i.state.finish_node();
        return (Some(item), origin, line, None);
    }
    let (fixity, kind) = fixity(item.payload_view().spelling().unwrap()).unwrap();
    item.emit_remaining(&mut *i.state, kind);
    (item, origin, line) = i
        .token(|lex| Some(next_item(lex, origin, line, fence)))
        .unwrap();
    let mut operator_name = None;
    let mut left = None;
    let mut right = None;
    use OperatorHeaderRole::{DefinitionIntroducer, LeftBindingPower, Name, RightBindingPower};
    let roles: &[OperatorHeaderRole] = match fixity {
        OperatorFixity::Prefix => &[Name, RightBindingPower, DefinitionIntroducer],
        OperatorFixity::Suffix => &[Name, LeftBindingPower, DefinitionIntroducer],
        OperatorFixity::Infix => &[
            Name,
            LeftBindingPower,
            RightBindingPower,
            DefinitionIntroducer,
        ],
        OperatorFixity::Nullfix => &[Name, DefinitionIntroducer],
    };
    let mut equals_end = None;
    let mut pending = Some(item);
    for &role in roles {
        item = pending
            .take()
            .expect("each header slot retains one current Item");
        let (next, next_origin, next_line, admitted) =
            required(i.rb(), item, origin, line, fence, role);
        (item, origin, line) = (next, next_origin, next_line);
        if !admitted {
            pending = Some(item);
            continue;
        }
        item.emit_all_remaining_leading(&mut *i.state);
        let text = item.payload_view().spelling().unwrap();
        match role {
            OperatorHeaderRole::Name => {
                operator_name = Some(name(text).unwrap().to_owned());
                i.state.start_node(SyntaxKind::OperatorName.into());
                i.state.token(SyntaxKind::LParen.into(), "(");
                i.state
                    .token(SyntaxKind::Operator.into(), name(text).unwrap());
                i.state.token(SyntaxKind::RParen.into(), ")");
                i.state.finish_node();
            }
            OperatorHeaderRole::LeftBindingPower | OperatorHeaderRole::RightBindingPower => {
                let value = power(text);
                if role == OperatorHeaderRole::LeftBindingPower {
                    left = value;
                } else {
                    right = value;
                }
                i.state.start_node(SyntaxKind::BindingPower.into());
                for (index, component) in text.split('.').enumerate() {
                    if index > 0 {
                        i.state.token(SyntaxKind::Dot.into(), ".");
                    }
                    i.state.token(SyntaxKind::Integer.into(), component);
                }
                i.state.finish_node();
            }
            OperatorHeaderRole::DefinitionIntroducer => {
                equals_end = Some(origin);
                item.emit_remaining(&mut *i.state, SyntaxKind::Equals);
                break;
            }
            OperatorHeaderRole::Fixity => unreachable!(),
        }
        (item, origin, line) = i
            .token(|lex| Some(next_slot_item(lex, origin, line, fence, false)))
            .unwrap();
        pending = Some(item);
    }
    i.state.finish_node();
    let fact = (|| {
        let powers = match fixity {
            OperatorFixity::Prefix => BindingPowers::prefix(right?),
            OperatorFixity::Suffix => BindingPowers::suffix(left?),
            OperatorFixity::Infix => BindingPowers::infix(left?, right?),
            OperatorFixity::Nullfix => BindingPowers::nullfix(),
        };
        Some(HeaderOperator::new(
            start..equals_end?,
            operator_name?,
            fixity,
            visibility,
            lazy,
            powers,
        ))
    })();
    (pending, origin, line, fact)
}
