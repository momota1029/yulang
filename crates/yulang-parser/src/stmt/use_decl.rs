use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::lex::{Lex, SyntaxKind, TriviaInfo};
use crate::parse::DelimitedListMachine;
use crate::sink::EventSink;

use super::use_scan::{UseTag, scan_use_tok};

pub(super) fn parse_use_decl<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    visibility: Option<Lex>,
    decl_kw: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    i.env.state.sink.start(SyntaxKind::UseDecl);
    if let Some(vis) = visibility {
        i.env.state.sink.lex(&vis);
    }
    let after_kw = decl_kw.trailing_trivia_info();
    i.env.state.sink.lex(&decl_kw);

    let result = parse_use_spec(i.rb(), after_kw);

    i.env.state.sink.finish();
    result
}

/// use の中身をパースする。
fn parse_use_spec<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    if matches!(leading_info, TriviaInfo::Newline { .. }) {
        return Some(Either::Left(leading_info));
    }

    let Some(first) = scan_use_tok(leading_info, i.rb()) else {
        return Some(Either::Left(leading_info));
    };

    match first.tag {
        UseTag::BraceL => {
            let after = UseGroupMachine.parse_brace_group(i.rb(), first.lex)?;
            parse_use_alias(i, after)
        }
        UseTag::Ident => {
            i.env.state.sink.lex(&first.lex);
            let after = first.lex.trailing_trivia_info();
            parse_use_after_segment(i, after)
        }
        UseTag::ParenL => parse_use_operator_segment(i, first.lex),
        UseTag::Stop | UseTag::BraceR => Some(Either::Right(first.lex)),
        _ => {
            emit_invalid(i.rb(), first.lex);
            Some(Either::Left(TriviaInfo::None))
        }
    }
}

/// ident セグメントの直後の処理（`/`, `::`, `as`, 停止）
fn parse_use_after_segment<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    if matches!(leading_info, TriviaInfo::Newline { .. }) {
        return Some(Either::Left(leading_info));
    }

    let Some(sep) = scan_use_tok(leading_info, i.rb()) else {
        return Some(Either::Left(leading_info));
    };

    match sep.tag {
        UseTag::Slash => {
            i.env.state.sink.lex(&sep.lex);
            let after = sep.lex.trailing_trivia_info();
            parse_use_after_slash_or_colon_colon(i, after)
        }
        UseTag::ColonColon => {
            i.env.state.sink.lex(&sep.lex);
            let after = sep.lex.trailing_trivia_info();
            parse_use_after_slash_or_colon_colon(i, after)
        }
        UseTag::As => {
            i.env.state.sink.lex(&sep.lex);
            let after = sep.lex.trailing_trivia_info();
            parse_use_alias_ident(i, after)
        }
        _ => Some(Either::Right(sep.lex)),
    }
}

/// `/` または `::` の直後の処理
fn parse_use_after_slash_or_colon_colon<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    if matches!(leading_info, TriviaInfo::Newline { .. }) {
        return Some(Either::Left(leading_info));
    }

    let Some(next) = scan_use_tok(leading_info, i.rb()) else {
        return Some(Either::Left(leading_info));
    };

    match next.tag {
        UseTag::Ident => {
            i.env.state.sink.lex(&next.lex);
            let after = next.lex.trailing_trivia_info();
            parse_use_after_segment(i, after)
        }
        UseTag::BraceL => {
            let after = UseGroupMachine.parse_brace_group(i.rb(), next.lex)?;
            parse_use_alias(i, after)
        }
        UseTag::Glob => {
            i.env.state.sink.lex(&next.lex);
            let after = next.lex.trailing_trivia_info();
            parse_use_after_glob(i, after)
        }
        UseTag::ParenL => parse_use_operator_segment(i, next.lex),
        _ => {
            emit_invalid(i.rb(), next.lex);
            Some(Either::Left(TriviaInfo::None))
        }
    }
}

fn parse_use_operator_segment<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    open: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    let after = parse_use_operator_name(i.rb(), open)?;
    parse_use_after_segment(i, after)
}

fn parse_use_operator_name<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    open: Lex,
) -> Option<TriviaInfo> {
    i.env.state.sink.lex(&open);
    let Some(op) = scan_use_tok(open.trailing_trivia_info(), i.rb()) else {
        return Some(open.trailing_trivia_info());
    };
    match op.tag {
        UseTag::Ident | UseTag::Op | UseTag::Glob => {
            i.env.state.sink.push(SyntaxKind::OpName, &op.lex.text);
        }
        _ => {
            emit_invalid(i.rb(), op.lex);
            return Some(TriviaInfo::None);
        }
    }

    let Some(close) = scan_use_tok(op.lex.trailing_trivia_info(), i.rb()) else {
        return Some(op.lex.trailing_trivia_info());
    };
    if close.tag != UseTag::ParenR {
        emit_invalid(i.rb(), close.lex);
        return Some(TriviaInfo::None);
    }
    i.env.state.sink.lex(&close.lex);
    Some(close.lex.trailing_trivia_info())
}

fn parse_use_after_glob<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    if matches!(leading_info, TriviaInfo::Newline { .. }) {
        return Some(Either::Left(leading_info));
    }

    let Some(next) = scan_use_tok(leading_info, i.rb()) else {
        return Some(Either::Left(leading_info));
    };

    match next.tag {
        UseTag::As => {
            i.env.state.sink.lex(&next.lex);
            let after = next.lex.trailing_trivia_info();
            parse_use_alias_ident(i, after)
        }
        UseTag::Without => {
            i.env.state.sink.lex(&next.lex);
            parse_use_without_list(i, next.lex.trailing_trivia_info())
        }
        _ => Some(Either::Right(next.lex)),
    }
}

fn parse_use_without_list<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    if matches!(leading_info, TriviaInfo::Newline { .. }) {
        return Some(Either::Left(leading_info));
    }

    let Some(item) = scan_use_tok(leading_info, i.rb()) else {
        return Some(Either::Left(leading_info));
    };

    match item.tag {
        UseTag::Ident | UseTag::Glob => {
            i.env.state.sink.lex(&item.lex);
            parse_use_without_after_item(i, item.lex.trailing_trivia_info())
        }
        UseTag::ParenL => {
            let after = parse_use_operator_name(i.rb(), item.lex)?;
            parse_use_without_after_item(i, after)
        }
        UseTag::BraceL => UseGroupMachine
            .parse_brace_group(i, item.lex)
            .map(Either::Left),
        UseTag::Stop | UseTag::BraceR => Some(Either::Right(item.lex)),
        _ => {
            emit_invalid(i.rb(), item.lex);
            Some(Either::Left(TriviaInfo::None))
        }
    }
}

fn parse_use_without_after_item<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    if matches!(leading_info, TriviaInfo::Newline { .. }) {
        return Some(Either::Left(leading_info));
    }

    let Some(next) = scan_use_tok(leading_info, i.rb()) else {
        return Some(Either::Left(leading_info));
    };

    match next.tag {
        UseTag::Comma => {
            i.env.state.sink.lex(&next.lex);
            parse_use_without_list(i, next.lex.trailing_trivia_info())
        }
        _ => Some(Either::Right(next.lex)),
    }
}

/// パスの末尾で `as alias` を処理（なければそのまま返す）
fn parse_use_alias<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    if matches!(leading_info, TriviaInfo::Newline { .. }) {
        return Some(Either::Left(leading_info));
    }

    let Some(next) = scan_use_tok(leading_info, i.rb()) else {
        return Some(Either::Left(leading_info));
    };

    match next.tag {
        UseTag::As => {
            i.env.state.sink.lex(&next.lex);
            let after = next.lex.trailing_trivia_info();
            parse_use_alias_ident(i, after)
        }
        _ => Some(Either::Right(next.lex)),
    }
}

/// `as` の後の alias ident
fn parse_use_alias_ident<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    if matches!(leading_info, TriviaInfo::Newline { .. }) {
        return Some(Either::Left(leading_info));
    }

    let Some(alias) = scan_use_tok(leading_info, i.rb()) else {
        return Some(Either::Left(leading_info));
    };

    match alias.tag {
        UseTag::Ident => {
            i.env.state.sink.lex(&alias.lex);
            parse_use_alias(i, alias.lex.trailing_trivia_info())
        }
        UseTag::Stop => Some(Either::Right(alias.lex)),
        _ => {
            emit_invalid(i.rb(), alias.lex);
            Some(Either::Left(TriviaInfo::None))
        }
    }
}

/// `{ item, item, ... }` を `BraceGroup` ノードとしてパースする machine。
///
/// `DelimitedListMachine` を実装することで：
/// - `,` が自動的に `Separator` ノードに包まれる
/// - 改行が暗黙の区切りとして扱われる
/// - `}` で終了
struct UseGroupMachine;

impl UseGroupMachine {
    /// `BraceGroup` ノードを開始・終了しながら `parse_delimited_list` を呼ぶ。
    fn parse_brace_group<I: EventInput, S: EventSink>(
        &mut self,
        mut i: In<I, S>,
        open_lex: Lex,
    ) -> Option<TriviaInfo> {
        i.env.state.sink.start(SyntaxKind::BraceGroup);
        let after = self.parse_delimited_list(i.rb(), open_lex)?;
        i.env.state.sink.finish();
        Some(after)
    }
}

impl<I: EventInput, S: EventSink> DelimitedListMachine<I, S> for UseGroupMachine {
    fn end_kind(&self) -> SyntaxKind {
        SyntaxKind::BraceR
    }

    fn is_group_sep(&self, kind: SyntaxKind) -> bool {
        matches!(kind, SyntaxKind::Comma)
    }

    /// `{}` 内では改行はインデントに関係なく区切りとして扱う
    fn is_implicit_separator(&self, info: TriviaInfo, _base_indent: usize) -> bool {
        matches!(info, TriviaInfo::Newline { .. })
    }

    fn parse_item(
        &mut self,
        i: In<I, S>,
        leading_info: TriviaInfo,
        _base_indent: usize,
    ) -> Option<Either<TriviaInfo, Lex>> {
        // `{}` 内では改行はアイテム間の空白として扱う（セパレータは DelimitedListMachine が管理）
        let leading = match leading_info {
            TriviaInfo::Newline { .. } => TriviaInfo::Space,
            other => other,
        };
        parse_use_spec(i, leading)
    }
}

fn emit_invalid<I: EventInput, S: EventSink>(i: In<I, S>, lex: Lex) {
    i.env.state.sink.start(SyntaxKind::InvalidToken);
    i.env.state.sink.lex(&lex);
    i.env.state.sink.finish();
}
