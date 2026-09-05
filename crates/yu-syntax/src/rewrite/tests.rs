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
    item::{OperatorUse, Payload, TokenKind, TriviaKind},
    operator::{STOP_ARROW, STOP_COLON, STOP_ELSE, scan_operator, stops_for},
    pattern::{PATTERN_DEFAULT_STOPS, PATTERN_STOP_COLON, pattern_with_stops},
    state::Recover,
    statement::statement,
    type_expr::type_expr,
};

mod binding;
mod case_like;
mod for_statement;
mod if_expr;
mod lexical;
mod mod_decl;
mod operators;
mod owners;
mod pattern;
mod struct_decl;
mod tails;
mod type_decl;
mod type_expr;
mod use_decl;
mod yumark;

fn run(source: &str) -> (GreenNode, Option<TailExit>) {
    let operators = OperatorTable::empty();
    run_with(source, &operators)
}

fn run_with(source: &str, operators: &OperatorTable) -> (GreenNode, Option<TailExit>) {
    let mut input = source;
    let mut recover = Recover::new(operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = expr(In::new(&mut input, &mut recover, &mut builder));
    if let Some(Err(Either::Right(end))) = &exit {
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
    let exit = Some(statement(
        In::new(&mut input, &mut recover, &mut builder),
        0,
        stops,
    ));
    if let Some(Err(Either::Right(end))) = &exit {
        emit_end(&mut builder, end);
    }
    builder.finish_node();
    (builder.finish(), exit)
}

fn run_type(source: &str) -> (GreenNode, Option<TailExit>) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = type_expr(In::new(&mut input, &mut recover, &mut builder));
    if let Some(Err(Either::Right(end))) = &exit {
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
    let exit = pattern_with_stops(In::new(&mut input, &mut recover, &mut builder), stops);
    if let Err(Either::Right(end)) = &exit {
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
