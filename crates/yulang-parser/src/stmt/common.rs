use chasa::Back as _;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::lex::{Lex, SyntaxKind, TriviaInfo};
use crate::scan::trivia::scan_trivia;
use crate::scan::{
    scan_ident_or_keyword, scan_number, scan_punct_expr, scan_sigil_ident, scan_unknown,
};
use crate::sink::EventSink;

pub(super) fn scan_stmt_lex<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Lex> {
    let (kind, text) = i.choice((
        scan_sigil_ident,
        scan_number,
        scan_ident_or_keyword,
        scan_punct_expr,
        scan_unknown,
    ))?;
    let trailing = i.run(scan_trivia)?;
    Some(Lex::new(leading_info, kind, text, trailing))
}

pub(super) fn peek_stmt_lex<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Lex> {
    let checkpoint = i.checkpoint();
    let tok = scan_stmt_lex(leading_info, i.rb())?;
    i.rollback(checkpoint);
    Some(tok)
}

pub(super) fn emit_missing_invalid<I: EventInput, S: EventSink>(i: In<I, S>) {
    i.env.state.sink.start(SyntaxKind::InvalidToken);
    i.env.state.sink.finish();
}
