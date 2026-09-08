use chasa_recover::In;
use rowan::GreenNode;

use super::output::RewriteOutput as GreenNodeBuilder;

use crate::{
    SyntaxKind, SyntaxNode,
    operator::{BindingPower, OperatorDeclaration, OperatorFixities, OperatorTable},
    scan::operator::OperatorSite,
    session::CommittedRecoveryRecord,
};

use super::{
    RewriteIn, Stops,
    act_decl::act_declaration_witness,
    cast_decl::cast_declaration_witness,
    current_item::LineEntry,
    declaration_companion::declaration_companion_witness,
    declaration_variant::{VariantSequenceForm, declaration_variant_sequence_witness},
    driver::{Either, NormalizedExit, TailExit, expr, expr_normalized, token_kind},
    emit::emit_end,
    enum_decl::enum_declaration_witness,
    error_decl::error_declaration_witness,
    impl_decl::impl_declaration_witness,
    item::{Item, OperatorUse, PhysicalLeadingTrivia, TokenKind, Trivia, TriviaKind},
    operator::{STOP_ARROW, STOP_COLON, STOP_ELSE, scan_operator, stops_for},
    pattern::{PATTERN_DEFAULT_STOPS, PATTERN_STOP_COLON, pattern_normalized, pattern_with_stops},
    role_decl::role_declaration_witness,
    state::Recover,
    statement::{statement, statement_normalized},
    type_expr::{type_expr, type_expr_normalized},
    yumark::FenceBoundary,
    yumark_cell::{accepted_identifier_statement_witness, yulang_code_cell_witness},
};

mod act_decl;
mod ambient_claim;
mod binding;
mod case_like;
mod cast_decl;
mod colon_sequence;
mod colon_with_recovery;
mod declaration_companion;
mod declaration_variant;
mod delimited_recovery;
mod derives;
mod enum_decl;
mod error_decl;
mod expression_recovery;
mod fixed_tail_recovery;
mod for_statement;
mod if_expr;
mod impl_decl;
mod indented_recovery;
mod lexical;
mod literal;
mod mod_decl;
mod normalized;
mod operators;
mod output;
mod owners;
mod pattern;
mod recovery_output;
mod role_decl;
mod rule;
mod rule_expression_list_recovery;
mod rule_literal_recovery;
mod statement;
mod string_literal_recovery;
mod struct_decl;
mod tails;
mod type_decl;
mod type_expr;
mod use_decl;
mod virtual_statement_block;
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

fn finish_with_discarded_recoveries(builder: GreenNodeBuilder<'_>) -> GreenNode {
    builder.finish_with_recoveries().0
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
    (finish_with_discarded_recoveries(builder), exit)
}

fn run_normalized<'source>(
    source: &'source str,
    operators: &OperatorTable,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, Option<NormalizedExit>, &'source str) {
    let mut input = source;
    let mut recover = Recover::new(operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = expr_normalized(
        In::new(&mut input, &mut recover, &mut builder),
        None,
        0,
        0,
        super::driver::MlMode::All,
        super::statement::StatementLineHandoff::OrdinaryLayout,
        item_origin,
        line_entry,
        fence,
        Some(crate::rewrite::ambient_claim::AmbientClaimView::root_statement(0)).into(),
        None,
    );
    builder.finish_node();
    (finish_with_discarded_recoveries(builder), exit, input)
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
    (finish_with_discarded_recoveries(builder), exit)
}

fn run_statement_normalized<'source>(
    source: &'source str,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, NormalizedExit, &'source str) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = statement_normalized(
        In::new(&mut input, &mut recover, &mut builder),
        0,
        0,
        item_origin,
        line_entry,
        fence,
        Some(crate::rewrite::ambient_claim::AmbientClaimView::root_statement(0)).into(),
        Some(crate::rewrite::sequence::SequenceOwner::RootStatement),
    );
    builder.finish_node();
    (finish_with_discarded_recoveries(builder), exit, input)
}

fn run_declaration_variant<'source>(
    source: &'source str,
    form: VariantSequenceForm,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, Option<NormalizedExit>, &'source str) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = declaration_variant_sequence_witness(
        In::new(&mut input, &mut recover, &mut builder),
        form,
        0,
        item_origin,
        line_entry,
        fence,
    );
    builder.finish_node();
    (finish_with_discarded_recoveries(builder), exit, input)
}

fn run_declaration_companion<'source>(
    source: &'source str,
    baseline: usize,
    caller_stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, Option<NormalizedExit>, &'source str) {
    let operators = OperatorTable::empty();
    run_declaration_companion_with(
        source,
        &operators,
        baseline,
        caller_stops,
        item_origin,
        line_entry,
        fence,
    )
}

fn run_enum_declaration<'source>(
    source: &'source str,
    caller_stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, Option<NormalizedExit>, &'source str) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = enum_declaration_witness(
        In::new(&mut input, &mut recover, &mut builder),
        0,
        caller_stops,
        super::statement::StatementLineHandoff::OrdinaryLayout,
        item_origin,
        line_entry,
        fence,
    );
    builder.finish_node();
    (finish_with_discarded_recoveries(builder), exit, input)
}

fn run_act_declaration<'source>(
    source: &'source str,
    caller_stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, Option<NormalizedExit>, &'source str) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = act_declaration_witness(
        In::new(&mut input, &mut recover, &mut builder),
        0,
        caller_stops,
        super::statement::StatementLineHandoff::OrdinaryLayout,
        item_origin,
        line_entry,
        fence,
    );
    builder.finish_node();
    (finish_with_discarded_recoveries(builder), exit, input)
}

fn run_role_declaration<'source>(
    source: &'source str,
    caller_stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, Option<NormalizedExit>, &'source str) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = role_declaration_witness(
        In::new(&mut input, &mut recover, &mut builder),
        0,
        caller_stops,
        super::statement::StatementLineHandoff::OrdinaryLayout,
        item_origin,
        line_entry,
        fence,
    );
    builder.finish_node();
    (finish_with_discarded_recoveries(builder), exit, input)
}

fn run_impl_declaration<'source>(
    source: &'source str,
    caller_stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, Option<NormalizedExit>, &'source str) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = impl_declaration_witness(
        In::new(&mut input, &mut recover, &mut builder),
        0,
        caller_stops,
        super::statement::StatementLineHandoff::OrdinaryLayout,
        item_origin,
        line_entry,
        fence,
    );
    builder.finish_node();
    (finish_with_discarded_recoveries(builder), exit, input)
}

fn run_cast_declaration<'source>(
    source: &'source str,
    caller_stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, Option<NormalizedExit>, &'source str) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = cast_declaration_witness(
        In::new(&mut input, &mut recover, &mut builder),
        0,
        caller_stops,
        super::statement::StatementLineHandoff::OrdinaryLayout,
        item_origin,
        line_entry,
        fence,
    );
    builder.finish_node();
    (finish_with_discarded_recoveries(builder), exit, input)
}

fn run_error_declaration<'source>(
    source: &'source str,
    caller_stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, Option<NormalizedExit>, &'source str) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = error_declaration_witness(
        In::new(&mut input, &mut recover, &mut builder),
        0,
        caller_stops,
        super::statement::StatementLineHandoff::OrdinaryLayout,
        item_origin,
        line_entry,
        fence,
    );
    builder.finish_node();
    (finish_with_discarded_recoveries(builder), exit, input)
}

#[allow(clippy::too_many_arguments)]
fn run_declaration_companion_with<'source>(
    source: &'source str,
    operators: &OperatorTable,
    baseline: usize,
    caller_stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, Option<NormalizedExit>, &'source str) {
    let mut input = source;
    let mut recover = Recover::new(operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = declaration_companion_witness(
        In::new(&mut input, &mut recover, &mut builder),
        baseline,
        caller_stops,
        item_origin,
        line_entry,
        fence,
    );
    builder.finish_node();
    (finish_with_discarded_recoveries(builder), exit, input)
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
    (finish_with_discarded_recoveries(builder), exit, input)
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
    let (green, exit, _) = run_type_with_recoveries(source, None);
    (green, exit)
}

fn run_type_with_recoveries<'frozen>(
    source: &str,
    frozen: Option<&'frozen [CommittedRecoveryRecord]>,
) -> (GreenNode, Option<TailExit>, Vec<CommittedRecoveryRecord>) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut builder = match frozen {
        Some(frozen) => GreenNodeBuilder::reconcile(frozen),
        None => GreenNodeBuilder::new(),
    };
    builder.start_node(SyntaxKind::Root.into());
    let mut exit = type_expr(In::new(&mut input, &mut recover, &mut builder));
    if let Some(Err(Either::Right(end))) = &mut exit {
        emit_end(&mut builder, end);
    }
    builder.finish_node();
    let (green, recoveries) = builder.finish_with_recoveries();
    (green, exit, recoveries)
}

fn run_type_normalized<'source>(
    source: &'source str,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, Option<NormalizedExit>, &'source str) {
    let (green, exit, remainder, _) =
        run_type_normalized_with_recoveries(source, item_origin, line_entry, fence, None);
    (green, exit, remainder)
}

fn run_type_normalized_with_recoveries<'source, 'frozen>(
    source: &'source str,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    frozen: Option<&'frozen [CommittedRecoveryRecord]>,
) -> (
    GreenNode,
    Option<NormalizedExit>,
    &'source str,
    Vec<CommittedRecoveryRecord>,
) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut builder = match frozen {
        Some(frozen) => GreenNodeBuilder::reconcile(frozen),
        None => GreenNodeBuilder::new(),
    };
    builder.start_node(SyntaxKind::Root.into());
    let exit = type_expr_normalized(
        In::new(&mut input, &mut recover, &mut builder),
        item_origin,
        line_entry,
        fence,
        Some(crate::rewrite::ambient_claim::AmbientClaimView::root_statement(0)).into(),
    );
    builder.finish_node();
    let (green, recoveries) = builder.finish_with_recoveries();
    (green, exit, input, recoveries)
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
    (finish_with_discarded_recoveries(builder), exit)
}

fn run_pattern_normalized<'source>(
    source: &'source str,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    stops: super::pattern::PatternStops,
) -> (GreenNode, NormalizedExit, &'source str) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = pattern_normalized(
        In::new(&mut input, &mut recover, &mut builder),
        item_origin,
        line_entry,
        fence,
        stops,
        Some(crate::rewrite::ambient_claim::AmbientClaimView::root_statement(0)).into(),
    );
    builder.finish_node();
    (finish_with_discarded_recoveries(builder), exit, input)
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
