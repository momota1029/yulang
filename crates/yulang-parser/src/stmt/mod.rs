use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::expr::parse_expr;
use crate::lex::{Lex, SyntaxKind, TriviaInfo};
use crate::mark::parse::{parse_doc_body_pub, parse_inline};
use crate::mark::scan::{BlockNudTag, MarkNudTag};
use crate::parse::emit_invalid;
use crate::pat::scan::scan_pat_nud;
use crate::scan::trivia::scan_trivia;
use crate::sink::EventSink;

mod act_decl;
mod binding;
mod block;
mod common;
mod enum_decl;
mod for_stmt;
mod impl_decl;
mod mod_decl;
mod op_def;
mod role_decl;
mod struct_decl;
mod type_decl;
mod use_decl;
mod use_scan;
mod where_clause;

pub(crate) use block::{parse_brace_stmt_block, parse_indent_stmt_block};

pub fn parse_statement<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Either<TriviaInfo, Lex>> {
    match parse_expr(leading_info, i.rb())? {
        Either::Left(next_info) => Some(Either::Left(next_info)),
        Either::Right(stop) => parse_statement_from_stop(i, stop),
    }
}

fn parse_statement_from_stop<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    stop: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    match stop.kind {
        SyntaxKind::My | SyntaxKind::Our | SyntaxKind::Pub => parse_visibility_stmt(i.rb(), stop),
        SyntaxKind::Use => use_decl::parse_use_decl(i, None, stop),
        SyntaxKind::Mod => mod_decl::parse_mod_decl(i, None, stop),
        SyntaxKind::Type => type_decl::parse_type_decl(i, None, stop),
        SyntaxKind::Struct => struct_decl::parse_struct_decl(i, None, stop),
        SyntaxKind::Enum => enum_decl::parse_enum_decl(i, None, stop),
        SyntaxKind::Role => role_decl::parse_role_decl(i, None, stop),
        SyntaxKind::Impl => impl_decl::parse_impl_decl(i, None, stop),
        SyntaxKind::Act => act_decl::parse_act_decl(i, None, stop),
        SyntaxKind::For => for_stmt::parse_for_stmt(i, stop),
        SyntaxKind::Prefix | SyntaxKind::Infix | SyntaxKind::Suffix | SyntaxKind::Nullfix => {
            op_def::parse_op_def_stmt(i, None, stop)
        }
        SyntaxKind::Where => where_clause::parse_where_clause(i.rb(), stop),
        SyntaxKind::DocComment => {
            i.env.state.sink.start(SyntaxKind::DocCommentDecl);
            i.env.state.sink.lex(&stop);
            if stop.text.as_ref() == "---" {
                // ブロック doc: `---` ... `---`
                i.env.state.sink.start(SyntaxKind::YmDoc);
                i.env.inline = false;
                let doc_stop = parse_doc_body_pub(i.rb())?;
                i.env.state.sink.finish(); // YmDoc
                if matches!(
                    doc_stop.nud.tag,
                    MarkNudTag::Block(BlockNudTag::DocBlockClose)
                ) {
                    if let Some(lex) = &doc_stop.nud.lex {
                        i.env.state.sink.push(SyntaxKind::DocComment, &lex.text);
                    }
                }
                i.env.state.sink.finish(); // DocCommentDecl
                // 閉じ `---` 後の余白を消費してその TriviaInfo を次の leading info にする
                let next_info = i
                    .run(scan_trivia)
                    .map(|t| t.info())
                    .unwrap_or(TriviaInfo::None);
                Some(Either::Left(next_info))
            } else {
                // ライン doc: `--` rest-of-line — YmParagraph で包む
                i.env.state.sink.start(SyntaxKind::YmDoc);
                i.env.inline = true;
                i.env.state.sink.start(SyntaxKind::YmParagraph);
                let inline_stop = parse_inline(i.rb())?;
                i.env.state.sink.finish(); // YmParagraph
                i.env.state.sink.finish(); // YmDoc
                i.env.state.sink.finish(); // DocCommentDecl
                // scan_mark が \n\n を含む trivia を全消費済み
                // blank_line は doc コメント後に伝播させない（後続 stmt には関係ない）
                let next_info = match inline_stop.trivia.info() {
                    TriviaInfo::Newline {
                        indent,
                        quote_level,
                        ..
                    } => TriviaInfo::Newline {
                        indent,
                        quote_level,
                        blank_line: false,
                    },
                    other => other,
                };
                Some(Either::Left(next_info))
            }
        }
        SyntaxKind::Semicolon
        | SyntaxKind::Comma
        | SyntaxKind::BraceR
        | SyntaxKind::ParenR
        | SyntaxKind::BracketR
        | SyntaxKind::YmFenceSigil => Some(Either::Right(stop)),
        _ => {
            let next_info = stop.trailing_trivia_info();
            emit_invalid(i.rb(), stop);
            Some(Either::Left(next_info))
        }
    }
}

fn parse_visibility_stmt<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    vis_kw: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    let next_info = vis_kw.trailing_trivia_info();

    let nud = scan_pat_nud(next_info, i.rb());

    let Some(nud) = nud else {
        return binding::parse_binding_stmt(i, vis_kw);
    };

    // stop トークンなら decl kw か Equal かで早期 dispatch
    use crate::pat::scan::PatNudTag;
    if matches!(nud.tag, PatNudTag::Stop) {
        let vis = Some(vis_kw);
        return match nud.lex.kind {
            SyntaxKind::Use => use_decl::parse_use_decl(i, vis, nud.lex),
            SyntaxKind::Mod => mod_decl::parse_mod_decl(i, vis, nud.lex),
            SyntaxKind::Type => type_decl::parse_type_decl(i, vis, nud.lex),
            SyntaxKind::Struct => struct_decl::parse_struct_decl(i, vis, nud.lex),
            SyntaxKind::Enum => enum_decl::parse_enum_decl(i, vis, nud.lex),
            SyntaxKind::Role => role_decl::parse_role_decl(i, vis, nud.lex),
            SyntaxKind::Impl => impl_decl::parse_impl_decl(i, vis, nud.lex),
            SyntaxKind::Act => act_decl::parse_act_decl(i, vis, nud.lex),
            SyntaxKind::Prefix | SyntaxKind::Infix | SyntaxKind::Suffix | SyntaxKind::Nullfix => {
                op_def::parse_op_def_stmt(i, vis, nud.lex)
            }
            // Equal や他の stop → binding に nud 結果（消費済み Equal）を渡す
            _ => binding::parse_binding_stmt_from_nud(i, vis.unwrap(), nud),
        };
    }

    // Atom 等（パターンの先頭）→ parse_pattern_from_nud で pat を構築してから binding へ
    binding::parse_binding_stmt_from_nud(i, vis_kw, nud)
}
