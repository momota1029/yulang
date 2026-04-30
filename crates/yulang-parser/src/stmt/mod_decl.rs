use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::lex::{Lex, SyntaxKind, TriviaInfo};
use crate::parse::emit_invalid;
use crate::sink::EventSink;

use super::block::{parse_brace_stmt_block, parse_decl_body_after_colon};
use super::common::scan_stmt_lex;

pub(super) fn parse_mod_decl<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    visibility: Option<Lex>,
    decl_kw: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    i.env.state.sink.start(SyntaxKind::ModDecl);
    if let Some(vis) = visibility {
        i.env.state.sink.lex(&vis);
    }
    i.env.state.sink.lex(&decl_kw);

    let mut leading_info = decl_kw.trailing_trivia_info();
    let Some(name) = scan_stmt_lex(leading_info, i.rb()) else {
        i.env.state.sink.finish();
        return Some(Either::Left(leading_info));
    };
    leading_info = name.trailing_trivia_info();
    if name.kind != SyntaxKind::Ident {
        emit_invalid(i.rb(), name);
        i.env.state.sink.finish();
        return Some(Either::Left(leading_info));
    }
    i.env.state.sink.lex(&name);

    let Some(punct) = scan_stmt_lex(leading_info, i.rb()) else {
        i.env.state.sink.finish();
        return Some(Either::Left(leading_info));
    };
    let base_indent = i.env.indent;
    let result = match punct.kind {
        SyntaxKind::Semicolon => {
            i.env.state.sink.lex(&punct);
            Either::Left(punct.trailing_trivia_info())
        }
        SyntaxKind::BraceL => {
            let next_info = parse_brace_stmt_block(i.rb(), punct)?;
            Either::Left(next_info)
        }
        SyntaxKind::Colon => {
            i.env.state.sink.lex(&punct);
            parse_decl_body_after_colon(i.rb(), punct.trailing_trivia_info(), base_indent)?
        }
        _ => {
            let next_info = punct.trailing_trivia_info();
            emit_invalid(i.rb(), punct);
            Either::Left(next_info)
        }
    };
    i.env.state.sink.finish();
    Some(result)
}
