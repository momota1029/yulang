use chasa::Back as _;
use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::expr::{parse_expr_from_nud, scan::scan_stmt_head_nud};
use crate::lex::{Lex, SyntaxKind, Trivia, TriviaInfo};
use crate::mark::parse::{parse_doc_body_pub, parse_inline};
use crate::mark::scan::{BlockNudTag, MarkNudTag};
use crate::parse::emit_invalid;
use crate::pat::scan::{PatNudTag, scan_pat_nud, scan_visibility_pat_nud};
use crate::scan::trivia::scan_trivia;
use crate::sink::EventSink;

mod act_decl;
mod binding;
mod block;
mod cast_decl;
mod common;
mod enum_decl;
mod error_decl;
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

pub(crate) use block::{
    parse_brace_stmt_block, parse_indent_stmt_block, parse_virtual_brace_stmt_block_until_close,
};
pub(crate) use common::{peek_stmt_lex, scan_stmt_lex};

pub fn parse_statement<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Either<TriviaInfo, Lex>> {
    let nud = scan_stmt_head_nud(leading_info, i.rb())?;
    match parse_expr_from_nud(None, i.rb(), nud)? {
        Ok(Either::Left(next_info)) => Some(Either::Left(next_info)),
        Ok(Either::Right(stop)) => parse_statement_from_stop(i, stop),
        Err(led) => Some(Either::Right(led.lex)),
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
        SyntaxKind::Error => error_decl::parse_error_decl(i, None, stop),
        SyntaxKind::Role => role_decl::parse_role_decl(i, None, stop),
        SyntaxKind::Impl => impl_decl::parse_impl_decl(i, None, stop),
        SyntaxKind::Cast => cast_decl::parse_cast_decl(i, None, stop),
        SyntaxKind::Act => act_decl::parse_act_decl(i, None, None, stop),
        SyntaxKind::For => for_stmt::parse_for_stmt(i, stop),
        SyntaxKind::Lazy => op_def::parse_lazy_op_def_stmt(i, None, stop),
        SyntaxKind::Prefix | SyntaxKind::Infix | SyntaxKind::Suffix | SyntaxKind::Nullfix => {
            op_def::parse_op_def_stmt(i, None, stop)
        }
        SyntaxKind::Where => where_clause::parse_where_clause(i.rb(), stop),
        SyntaxKind::DocComment => Some(Either::Left(parse_doc_comment_decl_from_stop(i, stop)?)),
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

pub(crate) fn parse_doc_comment_decl_from_stop<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    stop: Lex,
) -> Option<TriviaInfo> {
    i.env.state.sink.start(SyntaxKind::DocCommentDecl);
    i.env.state.sink.lex(&stop);
    if stop.text.as_ref() == "---" {
        i.env.state.sink.start(SyntaxKind::YmDoc);
        i.env.inline = false;
        let doc_stop = parse_doc_body_pub(i.rb())?;
        i.env.state.sink.finish();
        if matches!(
            doc_stop.nud.tag,
            MarkNudTag::Block(BlockNudTag::DocBlockClose)
        ) {
            if let Some(lex) = &doc_stop.nud.lex {
                i.env.state.sink.push(SyntaxKind::DocComment, &lex.text);
            }
        }
        i.env.state.sink.finish();
        let trailing = i.run(scan_trivia).unwrap_or_else(Trivia::empty);
        let info = trailing.info();
        i.env.state.sink.trivia(&trailing);
        return Some(info);
    }

    i.env.state.sink.start(SyntaxKind::YmDoc);
    i.env.inline = true;
    i.env.state.sink.start(SyntaxKind::YmParagraph);
    let inline_stop = parse_inline(i.rb())?;
    i.env.state.sink.finish();
    i.env.state.sink.finish();
    i.env.state.sink.finish();
    let info = match inline_stop.trivia.info() {
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
    i.env.state.sink.trivia(&inline_stop.trivia);
    Some(info)
}

fn parse_visibility_stmt<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    vis_kw: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    let next_info = vis_kw.trailing_trivia_info();

    if vis_kw.kind == SyntaxKind::My {
        let checkpoint = i.checkpoint();
        if let Some(nud) = scan_visibility_pat_nud(next_info, i.rb()) {
            if matches!(nud.tag, crate::pat::scan::PatNudTag::Stop)
                && nud.lex.kind == SyntaxKind::Act
                && my_contextual_act_decl_after_keyword(nud.lex.trailing_trivia_info(), i.rb())
            {
                return act_decl::parse_act_decl(i, Some(vis_kw), None, nud.lex);
            }
        }
        i.rollback(checkpoint);
    }

    let nud = if vis_kw.kind == SyntaxKind::My {
        scan_pat_nud(next_info, i.rb())
    } else {
        scan_visibility_pat_nud(next_info, i.rb())
    };

    let Some(nud) = nud else {
        return binding::parse_binding_stmt(i, vis_kw);
    };

    if contextual_host_act_modifier(&nud.lex)
        && let Some(act_kw) = scan_contextual_host_act(nud.lex.trailing_trivia_info(), i.rb())
    {
        let mut host = nud.lex;
        host.kind = SyntaxKind::Keyword;
        return act_decl::parse_act_decl(i, Some(vis_kw), Some(host), act_kw);
    }

    if contextual_host_operation_tier_modifier(&nud.lex) {
        let checkpoint = i.checkpoint();
        if let Some(operation_nud) =
            scan_contextual_host_operation_after_tier(nud.lex.trailing_trivia_info(), i.rb())
        {
            let mut tier = nud.lex;
            tier.kind = SyntaxKind::Keyword;
            return binding::parse_binding_stmt_from_nud_with_header_modifier(
                i,
                vis_kw,
                tier,
                operation_nud,
            );
        }
        i.rollback(checkpoint);
    }

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
            SyntaxKind::Error => error_decl::parse_error_decl(i, vis, nud.lex),
            SyntaxKind::Role => role_decl::parse_role_decl(i, vis, nud.lex),
            SyntaxKind::Impl => impl_decl::parse_impl_decl(i, vis, nud.lex),
            SyntaxKind::Cast => cast_decl::parse_cast_decl(i, vis, nud.lex),
            SyntaxKind::Act => act_decl::parse_act_decl(i, vis, None, nud.lex),
            SyntaxKind::Lazy => op_def::parse_lazy_op_def_stmt(i, vis, nud.lex),
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

fn contextual_host_act_modifier(lex: &Lex) -> bool {
    lex.kind == SyntaxKind::Ident && lex.text.as_ref() == "host"
}

fn contextual_host_operation_tier_modifier(lex: &Lex) -> bool {
    lex.kind == SyntaxKind::Ident
        && matches!(lex.text.as_ref(), "suspend_one_shot" | "suspend_multi_shot")
}

fn scan_contextual_host_operation_after_tier<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    i: In<I, S>,
) -> Option<crate::lex::Token<PatNudTag>> {
    if matches!(leading_info, TriviaInfo::Newline { .. } | TriviaInfo::None) {
        return None;
    }
    let nud = scan_visibility_pat_nud(leading_info, i)?;
    if matches!(nud.tag, PatNudTag::Atom)
        && matches!(nud.lex.kind, SyntaxKind::Ident | SyntaxKind::SigilIdent)
    {
        return Some(nud);
    }
    None
}

fn scan_contextual_host_act<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Lex> {
    if matches!(leading_info, TriviaInfo::Newline { .. } | TriviaInfo::None) {
        return None;
    }
    let next = peek_stmt_lex(leading_info, i.rb())?;
    if next.kind != SyntaxKind::Act {
        return None;
    }
    scan_stmt_lex(leading_info, i)
}

fn my_contextual_act_decl_after_keyword<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    i: In<I, S>,
) -> bool {
    peek_stmt_lex(leading_info, i)
        .is_some_and(|next| matches!(next.kind, SyntaxKind::Ident | SyntaxKind::SigilIdent))
}

/// ヘッダ先読みの 1 ステップの結果。
pub enum HeaderStep {
    /// use / op_def を読み終えた。次の leading_info で継続。
    Continue(TriviaInfo),
    /// 式、または use/op 以外の宣言が現れた。ヘッダはここで終了。
    Stop,
}

fn header_step(result: Option<Either<TriviaInfo, Lex>>) -> Option<HeaderStep> {
    match result? {
        Either::Left(next) => Some(HeaderStep::Continue(next)),
        Either::Right(_) => Some(HeaderStep::Stop),
    }
}

/// ヘッダ先読み: 先頭の use / op_def だけを読み、それ以外（式・定義）が来たら
/// 止まる。`parse_statement` の派生。op_def の body は読み捨てられる（呼び出し側で
/// `Env::header_only` を立てておく前提）。
pub fn parse_header_statement<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<HeaderStep> {
    let nud = scan_stmt_head_nud(leading_info, i.rb())?;
    match nud.lex.kind {
        SyntaxKind::Use => header_step(use_decl::parse_use_decl(i, None, nud.lex)),
        SyntaxKind::Lazy => header_step(op_def::parse_lazy_op_def_stmt(i, None, nud.lex)),
        SyntaxKind::Prefix | SyntaxKind::Infix | SyntaxKind::Suffix | SyntaxKind::Nullfix => {
            header_step(op_def::parse_op_def_stmt(i, None, nud.lex))
        }
        SyntaxKind::My | SyntaxKind::Our | SyntaxKind::Pub => parse_header_visibility(i, nud.lex),
        _ => Some(HeaderStep::Stop),
    }
}

/// `pub use` / `pub infix …` のような visibility 付き宣言をヘッダで拾う。
/// 中身が use/op_def なら継続、それ以外（定義・束縛）なら止まる。
fn parse_header_visibility<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    vis_kw: Lex,
) -> Option<HeaderStep> {
    let next_info = vis_kw.trailing_trivia_info();
    let Some(nud) = (if vis_kw.kind == SyntaxKind::My {
        scan_pat_nud(next_info, i.rb())
    } else {
        scan_visibility_pat_nud(next_info, i.rb())
    }) else {
        return Some(HeaderStep::Stop);
    };
    use crate::pat::scan::PatNudTag;
    if matches!(nud.tag, PatNudTag::Stop) {
        let vis = Some(vis_kw);
        return match nud.lex.kind {
            SyntaxKind::Use => header_step(use_decl::parse_use_decl(i, vis, nud.lex)),
            SyntaxKind::Lazy => header_step(op_def::parse_lazy_op_def_stmt(i, vis, nud.lex)),
            SyntaxKind::Prefix | SyntaxKind::Infix | SyntaxKind::Suffix | SyntaxKind::Nullfix => {
                header_step(op_def::parse_op_def_stmt(i, vis, nud.lex))
            }
            _ => Some(HeaderStep::Stop),
        };
    }
    Some(HeaderStep::Stop)
}
