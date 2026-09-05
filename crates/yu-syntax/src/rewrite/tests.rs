use chasa_recover::In;
use rowan::{GreenNode, GreenNodeBuilder};

use crate::{
    SyntaxKind, SyntaxNode,
    operator::{BindingPower, OperatorDeclaration, OperatorFixities, OperatorTable},
    scan::operator::OperatorSite,
};

use super::{
    RewriteIn, Stops,
    driver::{Either, TailExit, expr, token_kind},
    emit::emit_end,
    item::{Item, OperatorUse, PhysicalLeadingTrivia, TokenKind, Trivia, TriviaKind},
    operator::{STOP_ARROW, STOP_COLON, STOP_ELSE, scan_operator, stops_for},
    pattern::{PATTERN_DEFAULT_STOPS, PATTERN_STOP_COLON, pattern_with_stops},
    state::Recover,
    statement::statement,
    type_expr::type_expr,
    yumark_cell::{accepted_identifier_statement_witness, yulang_code_cell_witness},
};

mod binding;
mod case_like;
mod for_statement;
mod if_expr;
mod lexical;
mod literal;
mod mod_decl;
mod operators;
mod owners;
mod pattern;
mod rule;
mod struct_decl;
mod tails;
mod type_decl;
mod type_expr;
mod use_decl;
mod yumark;
mod yumark_cell;

fn ordinary_trivia(kind: TriviaKind, text: impl Into<Box<str>>) -> Trivia {
    let text = text.into();
    match kind {
        TriviaKind::Whitespace => Trivia::whitespace(text),
        TriviaKind::Newline => Trivia::newline(text),
        TriviaKind::LineComment => Trivia::line_comment(text),
        TriviaKind::BlockComment => Trivia::block_comment(text),
        TriviaKind::YmQuotePrefix => panic!("quote prefixes require physical Item construction"),
    }
}

fn physical_leading(
    parts: impl IntoIterator<Item = (TriviaKind, Box<str>)>,
) -> PhysicalLeadingTrivia {
    let mut leading = PhysicalLeadingTrivia::default();
    for (kind, text) in parts {
        if kind == TriviaKind::YmQuotePrefix {
            leading.push_quote_prefix(text);
        } else {
            leading.push_ordinary(ordinary_trivia(kind, text));
        }
    }
    leading
}

fn run(source: &str) -> (GreenNode, Option<TailExit>) {
    let operators = OperatorTable::empty();
    run_with(source, &operators)
}

fn run_with(source: &str, operators: &OperatorTable) -> (GreenNode, Option<TailExit>) {
    let mut input = source;
    let mut recover = Recover::new(operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let mut exit = expr(In::new(&mut input, &mut recover, &mut builder));
    if let Some(Err(Either::Right(end))) = &mut exit {
        emit_end(&mut builder, end);
    }
    builder.finish_node();
    (builder.finish(), exit)
}

fn run_statement(source: &str) -> (GreenNode, Option<TailExit>) {
    let operators = OperatorTable::empty();
    run_statement_with(source, &operators)
}

fn run_statement_with(source: &str, operators: &OperatorTable) -> (GreenNode, Option<TailExit>) {
    run_statement_with_stops(source, operators, 0)
}

fn run_statement_with_stops(
    source: &str,
    operators: &OperatorTable,
    stops: Stops,
) -> (GreenNode, Option<TailExit>) {
    let mut input = source;
    let mut recover = Recover::new(operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let mut exit = Some(statement(
        In::new(&mut input, &mut recover, &mut builder),
        0,
        stops,
    ));
    if let Some(Err(Either::Right(end))) = &mut exit {
        emit_end(&mut builder, end);
    }
    builder.finish_node();
    (builder.finish(), exit)
}

fn run_yumark_cell<'source>(
    source: &'source str,
    terminal: Item,
) -> (
    GreenNode,
    Result<super::item::PendingBoundary, TailExit>,
    &'source str,
) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = yulang_code_cell_witness(In::new(&mut input, &mut recover, &mut builder), terminal);
    builder.finish_node();
    (builder.finish(), exit, input)
}

fn run_fragmented_statement_successor(
    item: Item,
    successor: Item,
) -> (GreenNode, Result<super::item::PendingBoundary, TailExit>) {
    let operators = OperatorTable::empty();
    let mut input = "";
    let mut recover = Recover::new(&operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = accepted_identifier_statement_witness(
        In::new(&mut input, &mut recover, &mut builder),
        item,
        successor,
    );
    builder.finish_node();
    (builder.finish(), exit)
}

fn emit_pending_leading_text(item: &mut Item) -> String {
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    item.emit_all_remaining_leading(&mut builder);
    builder.finish_node();
    builder.finish().to_string()
}

fn emit_pending_leading_tokens(item: &mut Item) -> Vec<(SyntaxKind, String)> {
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    item.emit_all_remaining_leading(&mut builder);
    builder.finish_node();
    SyntaxNode::new_root(builder.finish())
        .children_with_tokens()
        .filter_map(|element| element.into_token())
        .map(|token| (token.kind(), token.text().to_owned()))
        .collect()
}

fn emit_terminal_leading_text(item: Item) -> (String, super::item::PendingBoundary) {
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let boundary = item.emit_terminal_boundary(&mut builder);
    builder.finish_node();
    (builder.finish().to_string(), boundary)
}

fn run_type(source: &str) -> (GreenNode, Option<TailExit>) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let mut exit = type_expr(In::new(&mut input, &mut recover, &mut builder));
    if let Some(Err(Either::Right(end))) = &mut exit {
        emit_end(&mut builder, end);
    }
    builder.finish_node();
    (builder.finish(), exit)
}

fn run_pattern(source: &str) -> (GreenNode, TailExit) {
    run_pattern_with_colon_stop(source, false)
}

fn run_pattern_with_colon_stop(source: &str, colon_stop: bool) -> (GreenNode, TailExit) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let stops = PATTERN_DEFAULT_STOPS | colon_stop.then_some(PATTERN_STOP_COLON).unwrap_or(0);
    let mut exit = pattern_with_stops(In::new(&mut input, &mut recover, &mut builder), stops);
    if let Err(Either::Right(end)) = &mut exit {
        emit_end(&mut builder, end);
    }
    builder.finish_node();
    (builder.finish(), exit)
}

fn dynamic_operator_table() -> OperatorTable {
    OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "~",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
        ),
        OperatorDeclaration::new(
            "+",
            OperatorFixities::new()
                .with_infix(BindingPower::scalar(40), BindingPower::new(40, [1])),
        ),
        OperatorDeclaration::new(
            "++",
            OperatorFixities::new().with_suffix(BindingPower::scalar(80)),
        ),
        OperatorDeclaration::new("?", OperatorFixities::new().with_nullfix()),
    ])
    .expect("distinct direct rewrite operator declarations")
}

fn scan_dynamic_operator<'source>(
    source: &'source str,
    operators: &OperatorTable,
    site: OperatorSite,
) -> (Option<OperatorUse>, &'source str) {
    scan_dynamic_operator_with_stops(source, operators, site, 0)
}

fn scan_dynamic_operator_with_stops<'source>(
    source: &'source str,
    operators: &OperatorTable,
    site: OperatorSite,
    stops: Stops,
) -> (Option<OperatorUse>, &'source str) {
    let mut remaining = source;
    let mut recover = Recover::new(operators);
    let operator = scan_operator(
        In::new(&mut remaining, &mut recover, ()),
        site,
        false,
        0,
        stops,
    )
    .map(|operator| operator.use_);
    (operator, remaining)
}

fn operator_chain_children(green: &GreenNode) -> Vec<SyntaxKind> {
    SyntaxNode::new_root(green.clone())
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer operator chain")
        .children()
        .map(|node| node.kind())
        .collect()
}
