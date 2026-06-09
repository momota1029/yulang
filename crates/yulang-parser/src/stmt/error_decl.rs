use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::lex::{Lex, SyntaxKind, TriviaInfo};
use crate::sink::EventSink;

use super::common::{peek_stmt_lex, scan_name_lex, scan_stmt_lex};
use super::type_decl::{finish_with_or_stmt_stop, scan_decl_type_vars};

pub(super) fn parse_error_decl<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    visibility: Option<Lex>,
    decl_kw: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    i.env.state.sink.start(SyntaxKind::ErrorDecl);
    if let Some(vis) = visibility {
        i.env.state.sink.lex(&vis);
    }
    i.env.state.sink.lex(&decl_kw);

    let mut leading_info = decl_kw.trailing_trivia_info();
    let Some(name) = scan_name_lex(leading_info, i.rb()) else {
        i.env.state.sink.finish();
        return Some(Either::Left(leading_info));
    };
    leading_info = name.trailing_trivia_info();
    i.env.state.sink.lex(&name);

    let vars = scan_decl_type_vars(i.rb(), leading_info, false)?;
    leading_info = vars.leading_info;

    if let Some(next) = peek_stmt_lex(leading_info, i.rb()) {
        match next.kind {
            SyntaxKind::BraceL => {
                let open = scan_stmt_lex(leading_info, i.rb())?;
                leading_info = super::enum_decl::parse_enum_variants_after_open(i.rb(), open)?;
            }
            SyntaxKind::Colon => {
                let colon = scan_stmt_lex(leading_info, i.rb())?;
                i.env.state.sink.lex(&colon);
                let base_indent = i.env.indent;
                leading_info = super::enum_decl::parse_enum_variants_indent_block(
                    i.rb(),
                    colon.trailing_trivia_info(),
                    base_indent,
                )?;
            }
            SyntaxKind::Equal => {
                let eq = scan_stmt_lex(leading_info, i.rb())?;
                i.env.state.sink.lex(&eq);
                match super::enum_decl::parse_enum_variants_inline(
                    i.rb(),
                    eq.trailing_trivia_info(),
                )? {
                    Either::Left(info) => leading_info = info,
                    Either::Right(stop) => {
                        i.env.state.sink.finish();
                        return Some(Either::Right(stop));
                    }
                }
            }
            _ => {}
        }
    }

    let out = finish_with_or_stmt_stop(i.rb(), leading_info, vars.with_kw)?;
    i.env.state.sink.finish();
    Some(out)
}
