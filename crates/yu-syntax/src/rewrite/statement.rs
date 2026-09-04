//! Direct canonical statements and their closed sequence owners.

use reborrow_generic::Reborrow as _;

use crate::{operator::BindingPower, syntax_kind::SyntaxKind};

use super::{
    RewriteIn, Stops,
    binding::{binding_statement, binding_statement_selected, is_binding_visibility},
    driver::{
        Either, MlMode, TailExit, continue_completed_tail, delimited_baseline, expr_from_nud,
        handoff, implicit_delimited_newline, indentation_after_newline, is_active_stop,
        is_separator, is_statement_nud, token_kind,
    },
    emit::{emit_leading_trivia, emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, Payload, TokenKind},
    lexer::{scan_trivia, statement_item_after_trivia},
    operator::stops_for,
    use_decl::{use_declaration, use_declaration_selected},
};

pub(super) fn statement(mut i: RewriteIn, baseline: usize, stops: Stops) -> TailExit {
    let leading = scan_trivia(i.rb());
    let item = statement_item_after_trivia(i.rb(), leading, baseline, stops);
    if is_canonical_statement_nud(i.rb(), &item, baseline) {
        canonical_statement(i, item, baseline, stops)
    } else {
        handoff(item)
    }
}

pub(super) fn canonical_statement(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: Stops,
) -> TailExit {
    debug_assert!(is_canonical_statement_nud(i.rb(), &item, baseline));
    i.state.start_node(SyntaxKind::Statement.into());
    let exit = if use_declaration_selected(i.rb(), &item, baseline) {
        use_declaration(i.rb(), item, baseline, stops)
    } else if binding_statement_selected(i.rb(), &item, baseline) {
        binding_statement(i.rb(), item, baseline, stops)
    } else {
        expr_from_nud(i.rb(), item, None, baseline, stops, MlMode::All)
    };
    i.state.finish_node();
    exit
}

pub(super) fn is_canonical_statement_nud(mut i: RewriteIn, item: &Item, baseline: usize) -> bool {
    if use_declaration_selected(i.rb(), item, baseline) {
        true
    } else if is_binding_visibility(item) {
        binding_statement_selected(i, item, baseline)
    } else {
        is_statement_nud(item)
    }
}

#[derive(Clone, Copy)]
enum StatementSequencePolicy {
    Indented { block_indent: usize },
    Braced,
}

/// The canonical indented sequence owns its opening trivia and equal-indent
/// separators; dedent and unimplemented statement starts remain pending Items.
pub(super) fn indented_statement_block(
    mut i: RewriteIn,
    base_indent: usize,
    stops: Stops,
) -> TailExit {
    let opening = scan_trivia(i.rb());
    let block_indent = indentation_after_newline(&opening)
        .filter(|&indentation| indentation > base_indent)
        .expect("C2 admission proved a strictly indented block opening");

    i.state
        .start_node(SyntaxKind::IndentedStatementBlock.into());
    emit_leading_trivia(&mut i, &opening);
    let item = statement_item_after_trivia(i.rb(), LeadingTrivia::default(), block_indent, stops);
    let exit = statement_sequence(
        i.rb(),
        item,
        StatementSequencePolicy::Indented { block_indent },
        block_indent,
        stops,
    );
    i.state.finish_node();
    exit
}

/// The braced-primary wrapper owns its delimiters and local separator stops;
/// the closed sequence helper owns normal statement progression for both
/// current block forms.
pub(super) fn braced_nud(
    mut i: RewriteIn,
    open: Item,
    threshold: Option<&BindingPower>,
    incoming_baseline: usize,
    outer_stops: Stops,
    outer_ml_mode: MlMode,
) -> TailExit {
    i.state
        .start_node(SyntaxKind::BracedStatementBlockExpression.into());
    emit_token_item(&mut i, open);
    let opening = scan_trivia(i.rb());
    let baseline = delimited_baseline(incoming_baseline, &opening);
    emit_leading_trivia(&mut i, &opening);
    let stops = stops_for(TokenKind::RBrace);
    let item = statement_item_after_trivia(i.rb(), LeadingTrivia::default(), baseline, stops);
    let exit = statement_sequence(
        i.rb(),
        item,
        StatementSequencePolicy::Braced,
        baseline,
        stops,
    );
    i.state.finish_node();
    continue_completed_tail(
        i,
        threshold,
        incoming_baseline,
        outer_stops,
        outer_ml_mode,
        exit,
    )
}

fn statement_sequence(
    mut i: RewriteIn,
    mut item: Item,
    policy: StatementSequencePolicy,
    baseline: usize,
    stops: Stops,
) -> TailExit {
    loop {
        match policy {
            StatementSequencePolicy::Indented { block_indent } => {
                let exit =
                    indented_statement_slot(i.rb(), item, baseline, block_indent, stops, true);
                item = match indented_statement_successor(i.rb(), exit, block_indent, stops) {
                    Ok(item) => item,
                    Err(exit) => return exit,
                };
            }
            StatementSequencePolicy::Braced => {
                if matches!(item.payload, Payload::Eof)
                    || token_kind(&item) == Some(TokenKind::RBrace)
                {
                    return braced_terminal(i, item);
                }
                let exit = braced_statement_slot(i.rb(), item, baseline, stops);
                item = match braced_statement_successor(i.rb(), exit, baseline, stops) {
                    Ok(item) => item,
                    Err(exit) => return exit,
                };
            }
        }
    }
}

fn indented_statement_successor(
    mut i: RewriteIn,
    exit: TailExit,
    block_indent: usize,
    stops: Stops,
) -> Result<Item, TailExit> {
    let Err(Either::Left(mut item)) = exit else {
        return Err(exit);
    };
    if indentation_after_newline(&item.leading) != Some(block_indent)
        || indented_statement_outer_boundary(i.rb(), &item, block_indent, stops)
    {
        return Err(handoff(item));
    }

    emit_separator_leading(&mut i, &mut item);
    Ok(item)
}

fn indented_statement_slot(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    block_indent: usize,
    stops: Stops,
    missing_on_boundary: bool,
) -> TailExit {
    if indented_statement_slot_boundary(i.rb(), &item, block_indent, stops) {
        if missing_on_boundary {
            let leading = std::mem::take(&mut item.leading);
            emit_missing(&mut i, leading);
        }
        return handoff(item);
    }
    if is_canonical_statement_nud(i.rb(), &item, baseline) {
        return canonical_statement(i, item, baseline, stops);
    }

    item = retry_indented_statement(i.rb(), item, baseline, block_indent, stops);
    if indented_statement_retry_boundary(i.rb(), &item, block_indent, stops) {
        return handoff(item);
    }
    debug_assert!(is_canonical_statement_nud(i.rb(), &item, baseline));
    canonical_statement(i, item, baseline, stops)
}

fn retry_indented_statement(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    block_indent: usize,
    stops: Stops,
) -> Item {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = statement_item_after_trivia(i.rb(), leading, baseline, stops);
        if indented_statement_retry_boundary(i.rb(), &item, block_indent, stops)
            || is_canonical_statement_nud(i.rb(), &item, baseline)
        {
            i.state.finish_node();
            return item;
        }
    }
}

fn indented_statement_slot_boundary(
    mut i: RewriteIn,
    item: &Item,
    block_indent: usize,
    stops: Stops,
) -> bool {
    matches!(item.payload, Payload::Eof)
        || is_separator(item)
        || is_active_stop(i.rb(), item, stops)
        || indentation_after_newline(&item.leading)
            .is_some_and(|indentation| indentation < block_indent)
}

fn indented_statement_retry_boundary(
    mut i: RewriteIn,
    item: &Item,
    block_indent: usize,
    stops: Stops,
) -> bool {
    indented_statement_slot_boundary(i.rb(), item, block_indent, stops)
        || indentation_after_newline(&item.leading) == Some(block_indent)
}

fn indented_statement_outer_boundary(
    mut i: RewriteIn,
    item: &Item,
    block_indent: usize,
    stops: Stops,
) -> bool {
    is_separator(item)
        || is_active_stop(i.rb(), item, stops)
        || indentation_after_newline(&item.leading)
            .is_some_and(|indentation| indentation < block_indent)
}

fn braced_terminal(mut i: RewriteIn, item: Item) -> TailExit {
    if token_kind(&item) == Some(TokenKind::RBrace) {
        emit_token_item(&mut i, item);
        return Ok(());
    }
    debug_assert!(matches!(item.payload, Payload::Eof));
    missing_brace_close(i, item)
}

fn braced_statement_slot(mut i: RewriteIn, item: Item, baseline: usize, stops: Stops) -> TailExit {
    if is_canonical_statement_nud(i.rb(), &item, baseline) {
        return canonical_statement(i, item, baseline, stops);
    }

    let item = retry_braced_statement(i.rb(), item, baseline, stops);
    if braced_statement_boundary(&item, baseline) {
        handoff(item)
    } else if is_canonical_statement_nud(i.rb(), &item, baseline) {
        canonical_statement(i, item, baseline, stops)
    } else {
        handoff(item)
    }
}

fn retry_braced_statement(mut i: RewriteIn, mut item: Item, baseline: usize, stops: Stops) -> Item {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = statement_item_after_trivia(i.rb(), leading, baseline, stops);
        if braced_statement_boundary(&item, baseline)
            || is_canonical_statement_nud(i.rb(), &item, baseline)
        {
            i.state.finish_node();
            return item;
        }
    }
}

fn braced_statement_boundary(item: &Item, baseline: usize) -> bool {
    matches!(item.payload, Payload::Eof)
        || is_separator(item)
        || token_kind(item) == Some(TokenKind::RBrace)
        || implicit_delimited_newline(baseline, &item.leading)
}

fn braced_statement_successor(
    mut i: RewriteIn,
    exit: TailExit,
    baseline: usize,
    stops: Stops,
) -> Result<Item, TailExit> {
    match exit {
        Ok(()) => Err(Ok(())),
        Err(Either::Right(mut end)) => {
            if implicit_delimited_newline(baseline, &end.item.leading) {
                emit_separator_leading(&mut i, &mut end.item);
            }
            Err(missing_brace_close(i, end.item))
        }
        Err(Either::Left(mut item)) if implicit_delimited_newline(baseline, &item.leading) => {
            emit_separator_leading(&mut i, &mut item);
            Ok(item)
        }
        Err(Either::Left(item)) if token_kind(&item) == Some(TokenKind::RBrace) => {
            emit_token_item(&mut i, item);
            Err(Ok(()))
        }
        Err(Either::Left(item)) if is_separator(&item) => {
            Ok(braced_explicit_separator(i, item, baseline, stops))
        }
        Err(Either::Left(item)) if is_canonical_statement_nud(i.rb(), &item, baseline) => {
            emit_missing(&mut i, LeadingTrivia::default());
            Ok(item)
        }
        Err(Either::Left(item)) => Ok(item),
    }
}

fn braced_explicit_separator(
    mut i: RewriteIn,
    separator: Item,
    baseline: usize,
    stops: Stops,
) -> Item {
    i.state
        .start_node(SyntaxKind::BlockStatementSeparator.into());
    emit_token_item(&mut i, separator);
    let leading = scan_trivia(i.rb());
    let mut item = statement_item_after_trivia(i.rb(), leading, baseline, stops);
    let leading = std::mem::take(&mut item.leading);
    emit_leading_trivia(&mut i, &leading);
    i.state.finish_node();
    item
}

fn emit_separator_leading(i: &mut RewriteIn, item: &mut Item) {
    i.state
        .start_node(SyntaxKind::BlockStatementSeparator.into());
    let leading = std::mem::take(&mut item.leading);
    emit_leading_trivia(i, &leading);
    i.state.finish_node();
}

fn missing_brace_close(mut i: RewriteIn, mut item: Item) -> TailExit {
    let leading = std::mem::take(&mut item.leading);
    emit_missing(&mut i, leading);
    handoff(item)
}
