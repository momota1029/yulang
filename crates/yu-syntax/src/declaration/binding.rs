//! Direct canonical BindingStatement construction.

use crate::ambient_claim::AmbientClaimContext;
use crate::cst_output::RecoveryDraft;
use crate::recovery_record::{
    BindingRole, DeclarationRole, ExpectationSources, ExpectedSyntax, GrammarRole, RecoveryKind,
    RecoverySiteKey, SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax,
};
use reborrow_generic::Reborrow as _;
use std::sync::Arc;

use crate::{lexical::operator_scan::OperatorSite, syntax_kind::SyntaxKind};

use crate::{
    cst_output::emit::{
        emit_recovery_error_run, emit_recovery_missing, emit_token_item, token_syntax_kind,
    },
    cursor::SyntaxIn,
    expression::{expr_from_nud_normalized, is_nud_item},
    handoff::{Either, MlMode, NormalizedExit, complete, handoff},
    lexical::{
        current_item::{CurrentItem, LineEntry, current_item},
        expression_item::expression_item,
        item::{Item, LeadingTrivia, TokenKind},
        lexer::{
            introduced_body_indentation_normalized, is_exact_equals_source,
            scan_pattern_nud_payload, scan_statement_payload, source_declaration_head,
            source_identifier,
        },
        observation::{
            implicit_delimited_newline, is_active_stop, is_line_stop, is_separator, token_kind,
        },
        position::{advanced_origin, suffix_marker},
        stops::Stops,
        trivia::{TriviaObservation, observe_fenced_trivia},
        yumark::FenceBoundary,
    },
    pattern::{
        PATTERN_STOP_EQUALS, binding_target_from_entry_item_normalized, pattern_stops_from_owner,
    },
    statement::{StatementLineHandoff, indented_statement_block_normalized},
};

pub(crate) fn binding_statement_selected_lexical(
    source: &str,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    let Some(visibility) = visibility_word(item) else {
        return false;
    };
    if crate::declaration::use_decl::use_declaration_selected_lexical(
        source,
        item,
        item_origin,
        fence,
    ) {
        return false;
    }
    if crate::declaration::mod_decl::mod_declaration_selected_lexical(
        source,
        item,
        baseline,
        item_origin,
        fence,
    ) {
        return false;
    }
    if crate::declaration::struct_decl::struct_declaration_selected_lexical(
        source,
        item,
        baseline,
        item_origin,
        fence,
    ) {
        return false;
    }
    if crate::declaration::type_decl::type_declaration_selected_lexical(
        source,
        item,
        baseline,
        item_origin,
        fence,
    ) {
        return false;
    }
    binding_follower_normalized(source, visibility, baseline, item_origin, fence)
}

fn binding_follower_normalized(
    source: &str,
    visibility: &str,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    let TriviaObservation::Visible(first) =
        observe_fenced_trivia(source, item_origin, LineEntry::InLine, fence)
    else {
        return true;
    };
    if !first.present
        || first
            .indentation
            .is_some_and(|indentation| indentation <= baseline)
    {
        return true;
    }
    let Some((head, after_head)) = source_identifier(first.source) else {
        return true;
    };

    match head {
        "use" => true,
        "type" | "role" | "impl" | "cast" => false,
        "enum" | "error" | "act" => {
            visibility == "my"
                && !named_declaration_head_candidate_normalized(
                    source,
                    after_head,
                    baseline,
                    item_origin,
                    fence,
                )
        }
        "lazy" | "prefix" | "infix" | "suffix" | "nullfix" => {
            binding_definition_follows_normalized(source, after_head, baseline, item_origin, fence)
        }
        _ => true,
    }
}

fn observed_after_head<'a>(
    full_source: &'a str,
    after_head: &'a str,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> TriviaObservation<'a> {
    let consumed = full_source.len() - after_head.len();
    let origin = item_origin
        .checked_add(consumed)
        .expect("a declaration admission coordinate must fit usize");
    observe_fenced_trivia(after_head, origin, LineEntry::InLine, fence)
}

fn named_declaration_head_candidate_normalized(
    full_source: &str,
    after_head: &str,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    let TriviaObservation::Visible(observed) =
        observed_after_head(full_source, after_head, item_origin, fence)
    else {
        return false;
    };
    if !observed.present
        || observed
            .indentation
            .is_some_and(|indentation| indentation <= baseline)
    {
        return false;
    }
    source_declaration_head(observed.source)
}

fn binding_definition_follows_normalized(
    full_source: &str,
    after_head: &str,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    let TriviaObservation::Visible(observed) =
        observed_after_head(full_source, after_head, item_origin, fence)
    else {
        return false;
    };
    observed.present
        && observed
            .indentation
            .is_none_or(|indentation| indentation > baseline)
        && is_exact_equals_source(observed.source)
}

pub(crate) fn is_binding_visibility(item: &Item) -> bool {
    visibility_word(item).is_some()
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn binding_statement_normalized(
    mut i: SyntaxIn,
    visibility: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::BindingStatement.into());
    i.state.start_node(SyntaxKind::BindingHeader.into());
    emit_visibility(&mut i, visibility);

    let entry = suffix_marker(i.rb());
    let exit = binding_target_normalized(
        i.rb(),
        baseline,
        stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    item_origin = advanced_origin(item_origin, entry, i.rb());
    let mut item = match exit {
        NormalizedExit::Complete(Err(Either::Left(item)), next_line_entry) => {
            line_entry = next_line_entry;
            item
        }
        exit => {
            i.state.finish_node();
            i.state.finish_node();
            return exit;
        }
    };
    if item.payload_view().is_boundary() {
        i.state.finish_node();
        i.state.finish_node();
        return complete(handoff(item), line_entry);
    }
    if token_kind(&item) != Some(TokenKind::Equals)
        || implicit_delimited_newline(baseline, item.leading_view())
    {
        i.state.finish_node();
        i.state.finish_node();
        return complete(handoff(item), line_entry);
    }

    item.emit_all_remaining_leading(&mut *i.state);
    emit_token_item(&mut i, item);
    i.state.finish_node();

    i.state.start_node(SyntaxKind::BindingBody.into());
    let exit = binding_body_normalized(
        i.rb(),
        baseline,
        stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    );
    i.state.finish_node();
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn binding_target_normalized(
    mut i: SyntaxIn,
    baseline: usize,
    owner_stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let stops = pattern_stops_from_owner(owner_stops)
        | crate::pattern::PATTERN_STOP_COMMA
        | crate::pattern::PATTERN_STOP_SEMICOLON
        | PATTERN_STOP_EQUALS;
    let entry = suffix_marker(i.rb());
    let CurrentItem {
        mut item,
        next_line_entry,
    } = i
        .token(|lex| {
            current_item(
                lex,
                item_origin,
                line_entry,
                fence,
                |lex, leading, origin, fence, _| {
                    scan_pattern_nud_payload(lex, leading, origin, fence, stops)
                },
            )
        })
        .expect("binding Pattern payload scanning is total");
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    if item.payload_view().is_boundary()
        || item
            .leading_view()
            .indentation_after_newline()
            .is_some_and(|indentation| indentation <= baseline)
    {
        i.state.start_node(SyntaxKind::Pattern.into());
        emit_binding_missing(&mut i, BindingRole::Target, &item, item_origin);
        i.state.finish_node();
        return complete(handoff(item), next_line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    binding_target_from_entry_item_normalized(
        i,
        item,
        baseline,
        stops,
        line_handoff,
        item_origin,
        next_line_entry,
        fence,
        ambient,
    )
}

#[allow(clippy::too_many_arguments)]
fn binding_body_normalized(
    mut i: SyntaxIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    match introduced_body_indentation_normalized(i.rb(), item_origin, fence) {
        Some(indentation) if indentation > baseline => indented_statement_block_normalized(
            i,
            baseline,
            crate::recovery_record::GrammarRole::Declaration(
                crate::recovery_record::DeclarationRole::Binding(
                    crate::recovery_record::BindingRole::IndentedStatement,
                ),
            ),
            stops,
            item_origin,
            line_entry,
            fence,
            ambient,
        ),
        Some(_) => {
            let (item, item_origin, line_entry) = binding_statement_item_normalized(
                i.rb(),
                item_origin,
                line_entry,
                fence,
                baseline,
                stops,
            );
            emit_binding_missing(&mut i, BindingRole::Body, &item, item_origin);
            complete(handoff(item), line_entry)
        }
        None => inline_binding_body_normalized(
            i,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn inline_binding_body_normalized(
    mut i: SyntaxIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let (mut item, item_origin, line_entry) = expression_item(
        i.rb(),
        OperatorSite::Nud,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
    );
    if binding_body_boundary(i.rb(), &item, baseline, stops) {
        emit_binding_body_eof_leading(&mut i, &mut item, baseline, stops);
        emit_binding_missing(&mut i, BindingRole::Body, &item, item_origin);
        return complete(handoff(item), line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    if is_nud_item(&item) {
        return expr_from_nud_normalized(
            i,
            item,
            None,
            baseline,
            stops,
            MlMode::All,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }

    let (mut item, item_origin, line_entry) = retry_inline_binding_body_normalized(
        i.rb(),
        item,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    );
    if binding_body_boundary(i.rb(), &item, baseline, stops) {
        emit_binding_body_eof_leading(&mut i, &mut item, baseline, stops);
        return complete(handoff(item), line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    debug_assert!(is_nud_item(&item));
    expr_from_nud_normalized(
        i,
        item,
        None,
        baseline,
        stops,
        MlMode::All,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
fn retry_inline_binding_body_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    let start = item.extent(item_origin).recovery_range().start;
    emit_recovery_error_run(
        i.rb(),
        |run| loop {
            let kind = token_syntax_kind(token_kind(&item).expect("malformed Binding body token"));
            let end = run
                .emit_item_as(item, item_origin, kind)
                .recovery_range()
                .end;
            (item, item_origin, line_entry) = run.lexical(|lex| {
                crate::lexical::expression_item::scan_expression_item_lexical(
                    lex,
                    OperatorSite::Nud,
                    item_origin,
                    line_entry,
                    fence,
                    baseline,
                    stops,
                )
            });
            if binding_body_static_boundary(&item, baseline, stops)
                || run.lexical(|lex| {
                    crate::lexical::observation::is_active_stop_lex(lex, &item, stops)
                })
                || is_nud_item(&item)
            {
                run.append_unexpected(UnexpectedSyntax::Token {
                    range: start..end,
                    category: UnexpectedCategory::OtherCharacter,
                });
                return (item, item_origin, line_entry);
            }
        },
        |range, unexpected| {
            binding_recovery_draft(BindingRole::Body, RecoveryKind::Error, range, unexpected)
        },
    )
}

fn binding_body_boundary(mut i: SyntaxIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    binding_body_static_boundary(item, baseline, stops) || is_active_stop(i.rb(), item, stops)
}

fn binding_body_static_boundary(item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || is_separator(item)
        || is_line_stop(item, stops)
        || implicit_delimited_newline(baseline, item.leading_view())
}

fn emit_binding_body_eof_leading(i: &mut SyntaxIn, item: &mut Item, baseline: usize, stops: Stops) {
    if item.payload_view().is_eof()
        && !item.payload_view().is_boundary()
        && !is_line_stop(item, stops)
        && !implicit_delimited_newline(baseline, item.leading_view())
        && !is_active_stop(i.rb(), item, stops)
    {
        item.emit_eof_leading(&mut *i.state);
    }
}

fn emit_binding_missing(i: &mut SyntaxIn, role: BindingRole, item: &Item, origin: usize) {
    let at = item.payload_view().pending_boundary().map_or_else(
        || item.extent(origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    );
    emit_recovery_missing(i.rb(), LeadingTrivia::default(), at, |range| {
        binding_recovery_draft(role, RecoveryKind::Missing, range, Arc::from([]))
    });
}

fn binding_recovery_draft(
    role: BindingRole,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let expected = match role {
        BindingRole::Target => ExpectedSyntax::Pattern,
        BindingRole::Body => ExpectedSyntax::Expression,
        _ => unreachable!("inline Binding recovery"),
    };
    let role = GrammarRole::Declaration(DeclarationRole::Binding(role));
    RecoveryDraft::new(
        RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        Arc::from([SyntaxExpectation {
            role,
            expected,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        0,
    )
}

#[allow(clippy::too_many_arguments)]
fn binding_statement_item_normalized(
    mut i: SyntaxIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
) -> (Item, usize, LineEntry) {
    let entry = suffix_marker(i.rb());
    let CurrentItem {
        item,
        next_line_entry,
    } = i
        .token(|lex| {
            current_item(
                lex,
                item_origin,
                line_entry,
                fence,
                |lex, leading, origin, fence, _| {
                    scan_statement_payload(lex, leading, origin, fence, baseline, stops)
                },
            )
        })
        .expect("statement payload scanning is total");
    (
        item,
        advanced_origin(item_origin, entry, i),
        next_line_entry,
    )
}

fn visibility_word(item: &Item) -> Option<&str> {
    let payload = item.payload_view();
    assert!(
        !payload.is_boundary(),
        "a boundary is not a visibility word"
    );
    match (payload.token_kind(), payload.spelling()) {
        (Some(TokenKind::Identifier), Some(text)) if matches!(text, "my" | "our" | "pub") => {
            Some(text)
        }
        _ => None,
    }
}

fn emit_visibility(i: &mut SyntaxIn, item: Item) {
    debug_assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::Identifier)
    );
    let kind = match item.payload_view().spelling() {
        Some("my") => SyntaxKind::MyKw,
        Some("our") => SyntaxKind::OurKw,
        Some("pub") => SyntaxKind::PubKw,
        _ => unreachable!("the binding judge accepted only visibility words"),
    };
    item.emit_remaining(&mut *i.state, kind);
}
