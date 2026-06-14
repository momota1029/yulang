use std::fmt::Write as _;

use chasa::error::LatestSink;
use chasa::input::{In, Input as _, IsCut};
use either::Either;
use im::HashSet;
use reborrow_generic::Reborrow as _;
use yulang_parser::context::{Env, State};
use yulang_parser::expr::parse_expr;
use yulang_parser::lex::{SyntaxKind, TriviaInfo};
use yulang_parser::mark::parse::parse_doc;
use yulang_parser::op::standard_op_table;
use yulang_parser::pat::parse::parse_pattern;
use yulang_parser::scan::trivia::scan_trivia;
use yulang_parser::sink::{Event, EventSink, VecSink};
use yulang_parser::stmt::parse_statement;
use yulang_parser::typ::parse::parse_type;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParserMode {
    Expr,
    Pat,
    Stmt,
    Type,
    Mark,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseViewOutput {
    pub text: String,
    pub ok: bool,
}

pub fn run_parser_view(mode: ParserMode, source: &str) -> ParseViewOutput {
    let mut state: State<VecSink> = State::default();
    let mut input = source.with_counter(0usize);
    let mut errors = LatestSink::new();
    let mut cut_flag = false;
    let base_in = In::new(&mut input, &mut errors, IsCut::new(&mut cut_flag));
    let env = Env::new(&mut state, standard_op_table(), 0, HashSet::new());
    let mut i = base_in.set_env(env);

    let ok = if matches!(mode, ParserMode::Mark) {
        parse_doc(i.rb());
        true
    } else {
        let leading_info = i
            .run(scan_trivia)
            .map(|trivia| trivia.info())
            .unwrap_or(TriviaInfo::None);
        match mode {
            ParserMode::Expr => run_parse_expr(i.rb(), leading_info),
            ParserMode::Pat => run_parse_pat(i.rb(), leading_info),
            ParserMode::Stmt => run_parse_stmt(i.rb(), leading_info),
            ParserMode::Type => run_parse_type(i.rb(), leading_info),
            ParserMode::Mark => unreachable!(),
        }
    };

    let (events, lexs) = std::mem::take(&mut i.env.state.sink).into_parts();
    ParseViewOutput {
        text: format_parser_event_tree(&events, &lexs),
        ok,
    }
}

pub fn parse_mode(name: &str) -> Option<ParserMode> {
    match name {
        "expr" => Some(ParserMode::Expr),
        "pat" => Some(ParserMode::Pat),
        "stmt" => Some(ParserMode::Stmt),
        "type" => Some(ParserMode::Type),
        "mark" => Some(ParserMode::Mark),
        _ => None,
    }
}

fn format_parser_event_tree(events: &[Event], lexs: &[yulang_parser::lex::Lex]) -> String {
    let mut out = String::new();
    let mut indent = 0usize;
    let mut iter = lexs.iter();
    for event in events {
        match event {
            Event::Start(kind) => {
                let _ = writeln!(out, "{}{:?}", "  ".repeat(indent), kind);
                indent += 1;
            }
            Event::Lex(kind) => {
                let lex = iter.next();
                let (text, lead, trail) = match lex {
                    Some(lex) => (
                        format!("{:?}", lex.text.as_ref()),
                        format!("{:?}", lex.leading_trivia_info),
                        lex.trailing_trivia.parts().len(),
                    ),
                    None => ("<missing>".to_string(), "-".to_string(), 0),
                };
                let _ = writeln!(
                    out,
                    "{}{:?} {}  lead={} trail={}",
                    "  ".repeat(indent),
                    kind,
                    text,
                    lead,
                    trail
                );
            }
            Event::Finish => {
                indent = indent.saturating_sub(1);
            }
        }
    }
    out
}

fn run_parse_expr<I: yulang_parser::EventInput>(
    mut i: yulang_parser::context::In<I, VecSink>,
    leading_info: TriviaInfo,
) -> bool {
    let parsed = parse_expr(leading_info, i.rb());
    emit_parse_stop_if_any(i.rb(), parsed)
}

fn run_parse_pat<I: yulang_parser::EventInput>(
    mut i: yulang_parser::context::In<I, VecSink>,
    leading_info: TriviaInfo,
) -> bool {
    let parsed = parse_pattern(leading_info, i.rb());
    emit_parse_stop_if_any(i.rb(), parsed)
}

fn run_parse_type<I: yulang_parser::EventInput>(
    mut i: yulang_parser::context::In<I, VecSink>,
    leading_info: TriviaInfo,
) -> bool {
    let parsed = parse_type(leading_info, i.rb());
    emit_parse_stop_if_any(i.rb(), parsed)
}

fn run_parse_stmt<I: yulang_parser::EventInput>(
    mut i: yulang_parser::context::In<I, VecSink>,
    mut leading_info: TriviaInfo,
) -> bool {
    i.env.state.sink.start(SyntaxKind::IndentBlock);
    loop {
        let parsed = parse_statement(leading_info, i.rb());
        match parsed {
            Some(Either::Left(next)) => leading_info = next,
            Some(Either::Right(stop)) if stop.kind == SyntaxKind::Semicolon => {
                i.env.state.sink.start(SyntaxKind::Separator);
                i.env.state.sink.lex(&stop);
                i.env.state.sink.finish();
                leading_info = stop.trailing_trivia_info();
            }
            Some(Either::Right(stop)) => {
                i.env.state.sink.start(SyntaxKind::InvalidToken);
                i.env.state.sink.lex(&stop);
                i.env.state.sink.finish();
                leading_info = stop.trailing_trivia_info();
            }
            None => break,
        }
    }
    i.env.state.sink.finish();
    true
}

fn emit_parse_stop_if_any<I: yulang_parser::EventInput>(
    i: yulang_parser::context::In<I, VecSink>,
    parsed: Option<Either<TriviaInfo, yulang_parser::lex::Lex>>,
) -> bool {
    let ok = parsed.is_some();
    if let Some(Either::Right(stop)) = parsed {
        i.env.state.sink.start(SyntaxKind::InvalidToken);
        i.env.state.sink.lex(&stop);
        i.env.state.sink.finish();
    }
    ok
}
