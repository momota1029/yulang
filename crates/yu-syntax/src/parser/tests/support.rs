//! Shared test runners, builders and source fixtures.
pub(super) use chasa_recover::In;
pub(super) use rowan::GreenNode;

pub(super) use crate::parser::output::ParserOutput as GreenNodeBuilder;

pub(super) use crate::{
    SyntaxKind, SyntaxNode,
    operator::{BindingPower, OperatorDeclaration, OperatorFixities, OperatorTable},
    parser::input::operator::OperatorSite,
    session::CommittedRecoveryRecord,
};

pub(super) use crate::parser::{
    ParserIn, Stops,
    context::state::Recover,
    declaration::{
        act_decl::act_declaration_witness,
        cast_decl::cast_declaration_witness,
        declaration_companion::declaration_companion_witness,
        declaration_variant::{VariantSequenceForm, declaration_variant_sequence_witness},
        enum_decl::enum_declaration_witness,
        error_decl::error_declaration_witness,
        impl_decl::impl_declaration_witness,
        role_decl::role_declaration_witness,
    },
    expression::{expr, expr_normalized},
    handoff::{Either, NormalizedExit, TailExit},
    input::{
        current_item::LineEntry,
        item::{Item, OperatorUse, PhysicalLeadingTrivia, TokenKind, Trivia, TriviaKind},
        observation::token_kind,
        operator::{STOP_ARROW, STOP_COLON, STOP_ELSE, scan_operator, stops_for},
        yumark::FenceBoundary,
    },
    output::emit::emit_end,
    pattern::{PATTERN_DEFAULT_STOPS, PATTERN_STOP_COLON, pattern_normalized, pattern_with_stops},
    statement::{statement, statement_normalized},
    type_expr::{type_expr, type_expr_normalized},
};

pub(super) use crate::parser::tests::yumark_cell_witness::{
    accepted_identifier_statement_witness, yulang_code_cell_witness,
};

pub(super) fn ordinary_trivia(kind: TriviaKind, text: impl Into<Box<str>>) -> Trivia {
    let text = text.into();
    match kind {
        TriviaKind::Whitespace => Trivia::whitespace(text),
        TriviaKind::Newline => Trivia::newline(text),
        TriviaKind::LineComment => Trivia::line_comment(text),
        TriviaKind::BlockComment => Trivia::block_comment(text),
        TriviaKind::YmQuotePrefix => panic!("quote prefixes require physical Item construction"),
    }
}

pub(super) fn physical_leading(
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

pub(super) fn finish_with_discarded_recoveries(builder: GreenNodeBuilder<'_>) -> GreenNode {
    builder.finish_with_recoveries().0
}

pub(super) fn run(source: &str) -> (GreenNode, Option<TailExit>) {
    let operators = OperatorTable::empty();
    run_with(source, &operators)
}

pub(super) fn run_with(source: &str, operators: &OperatorTable) -> (GreenNode, Option<TailExit>) {
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

pub(super) fn run_normalized<'source>(
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
        crate::parser::handoff::MlMode::All,
        crate::parser::statement::StatementLineHandoff::OrdinaryLayout,
        item_origin,
        line_entry,
        fence,
        Some(crate::parser::context::ambient_claim::AmbientClaimView::root_statement(0)).into(),
        None,
    );
    builder.finish_node();
    (finish_with_discarded_recoveries(builder), exit, input)
}

pub(super) fn run_statement(source: &str) -> (GreenNode, Option<TailExit>) {
    let operators = OperatorTable::empty();
    run_statement_with(source, &operators)
}

pub(super) fn run_statement_with(
    source: &str,
    operators: &OperatorTable,
) -> (GreenNode, Option<TailExit>) {
    run_statement_with_stops(source, operators, 0)
}

pub(super) fn run_statement_with_stops(
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

pub(super) fn run_statement_normalized<'source>(
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
        Some(crate::parser::context::ambient_claim::AmbientClaimView::root_statement(0)).into(),
        Some(crate::parser::context::sequence::SequenceOwner::RootStatement),
    );
    builder.finish_node();
    (finish_with_discarded_recoveries(builder), exit, input)
}

pub(super) fn run_declaration_variant<'source>(
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

pub(super) fn run_declaration_companion<'source>(
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

pub(super) fn run_enum_declaration<'source>(
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
        crate::parser::statement::StatementLineHandoff::OrdinaryLayout,
        item_origin,
        line_entry,
        fence,
    );
    builder.finish_node();
    (finish_with_discarded_recoveries(builder), exit, input)
}

pub(super) fn run_act_declaration<'source>(
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
        crate::parser::statement::StatementLineHandoff::OrdinaryLayout,
        item_origin,
        line_entry,
        fence,
    );
    builder.finish_node();
    (finish_with_discarded_recoveries(builder), exit, input)
}

pub(super) fn run_role_declaration<'source>(
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
        crate::parser::statement::StatementLineHandoff::OrdinaryLayout,
        item_origin,
        line_entry,
        fence,
    );
    builder.finish_node();
    (finish_with_discarded_recoveries(builder), exit, input)
}

pub(super) fn run_impl_declaration<'source>(
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
        crate::parser::statement::StatementLineHandoff::OrdinaryLayout,
        item_origin,
        line_entry,
        fence,
    );
    builder.finish_node();
    (finish_with_discarded_recoveries(builder), exit, input)
}

pub(super) fn run_cast_declaration<'source>(
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
        crate::parser::statement::StatementLineHandoff::OrdinaryLayout,
        item_origin,
        line_entry,
        fence,
    );
    builder.finish_node();
    (finish_with_discarded_recoveries(builder), exit, input)
}

pub(super) fn run_error_declaration<'source>(
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
        crate::parser::statement::StatementLineHandoff::OrdinaryLayout,
        item_origin,
        line_entry,
        fence,
    );
    builder.finish_node();
    (finish_with_discarded_recoveries(builder), exit, input)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn run_declaration_companion_with<'source>(
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

pub(super) fn run_yumark_cell<'source>(
    source: &'source str,
    terminal: Item,
) -> (
    GreenNode,
    Result<crate::parser::input::item::PendingBoundary, TailExit>,
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

pub(super) fn run_fragmented_statement_successor(
    item: Item,
    successor: Item,
) -> (
    GreenNode,
    Result<crate::parser::input::item::PendingBoundary, TailExit>,
) {
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

pub(super) fn emit_pending_leading_text(item: &mut Item) -> String {
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    item.emit_all_remaining_leading(&mut builder);
    builder.finish_node();
    builder.finish().to_string()
}

pub(super) fn emit_pending_leading_tokens(item: &mut Item) -> Vec<(SyntaxKind, String)> {
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

pub(super) fn emit_terminal_leading_text(
    item: Item,
) -> (String, crate::parser::input::item::PendingBoundary) {
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let boundary = item.emit_terminal_boundary(&mut builder);
    builder.finish_node();
    (builder.finish().to_string(), boundary)
}

pub(super) fn run_type(source: &str) -> (GreenNode, Option<TailExit>) {
    let (green, exit, _) = run_type_with_recoveries(source, None);
    (green, exit)
}

pub(super) fn run_type_with_recoveries<'frozen>(
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

pub(super) fn run_type_normalized<'source>(
    source: &'source str,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, Option<NormalizedExit>, &'source str) {
    let (green, exit, remainder, _) =
        run_type_normalized_with_recoveries(source, item_origin, line_entry, fence, None);
    (green, exit, remainder)
}

pub(super) fn run_type_normalized_with_recoveries<'source, 'frozen>(
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
        Some(crate::parser::context::ambient_claim::AmbientClaimView::root_statement(0)).into(),
    );
    builder.finish_node();
    let (green, recoveries) = builder.finish_with_recoveries();
    (green, exit, input, recoveries)
}

pub(super) fn run_pattern(source: &str) -> (GreenNode, TailExit) {
    run_pattern_with_colon_stop(source, false)
}

pub(super) fn run_pattern_with_colon_stop(source: &str, colon_stop: bool) -> (GreenNode, TailExit) {
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

pub(super) fn run_pattern_normalized<'source>(
    source: &'source str,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    stops: crate::parser::pattern::PatternStops,
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
        Some(crate::parser::context::ambient_claim::AmbientClaimView::root_statement(0)).into(),
    );
    builder.finish_node();
    (finish_with_discarded_recoveries(builder), exit, input)
}

pub(super) fn dynamic_operator_table() -> OperatorTable {
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
    .expect("distinct direct parser operator declarations")
}

pub(super) fn scan_dynamic_operator<'source>(
    source: &'source str,
    operators: &OperatorTable,
    site: OperatorSite,
) -> (Option<OperatorUse>, &'source str) {
    scan_dynamic_operator_with_stops(source, operators, site, 0)
}

pub(super) fn scan_dynamic_operator_with_stops<'source>(
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

pub(super) fn operator_chain_children(green: &GreenNode) -> Vec<SyntaxKind> {
    SyntaxNode::new_root(green.clone())
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer operator chain")
        .children()
        .map(|node| node.kind())
        .collect()
}
