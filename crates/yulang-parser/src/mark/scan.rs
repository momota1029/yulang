use crate::EventInput;
use crate::context::In;
use crate::lex::{SyntaxKind, Trivia};
use crate::scan::trivia::scan_trivia;
use crate::sink::EventSink;
use chasa::parser::{SkipParserMut as _, SkipParserOnce as _};
use chasa::prelude::{any, choice, eoi, from_fn, item, one_of, tag};
use reborrow_generic::Reborrow as _;

// ---------------------------------------------------------------------------
// Nud tags
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InlineNudTag {
    Newline { indent: usize },
    Bang,
    Emphasis,
    Strong,
    OpenBracket,
    Backslash,
    SectionClose,
    CloseBracket,
    CloseBrace,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockNudTag {
    LineEnd,
    NewParagraph,
    Dequote { quote_level: usize, indent: usize },
    DocBlockClose,
    ListMinus,
    ListNum,
    Heading,
    Fence,
    BlockQuote,
    InputEnd,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MarkNudTag {
    Inline(InlineNudTag),
    Block(BlockNudTag),
}

// ---------------------------------------------------------------------------
// MarkNud<Tag>
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyntaxLex {
    pub text: Box<str>,
    pub kind: SyntaxKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MarkNud<Tag = MarkNudTag> {
    pub lex: Option<SyntaxLex>,
    pub tag: Tag,
}

// ---------------------------------------------------------------------------
// Mark
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct Mark {
    /// 行頭 prefix テキスト（スペース・`>`）
    pub text: Box<str>,
    pub trivia: Trivia,
    pub nud: MarkNud,
}

pub fn scan_mark<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<Mark> {
    let start = i.input.checkpoint();
    let start_idx = i.index();
    let env_inline = i.env.inline;
    let many_result = i.many_till(
        any.skip(),
        from_fn(|mut i: In<I, S>| {
            let at_start = i.index() == start_idx;
            let end = i.input.checkpoint();
            let trivia_opt = scan_trivia(i.rb());
            let trivia = trivia_opt?;
            if matches!(trivia.info(), crate::lex::TriviaInfo::Newline { .. }) {
                return Some((end, trivia));
            }
            // インライン sigil / EOI では常に停止
            if i.lookahead(choice((
                eoi.to(()),
                one_of("*![\\]}").to(()),
                (item('#').many1_skip(), item('.')).to(()),
            )))
            .is_some()
            {
                return Some((end, trivia));
            }
            // ブロック sigil はドキュメント先頭 (テキスト未蓄積) かつブロックモードのみ
            if at_start
                && !env_inline
                && i.lookahead(choice((
                    (item('#').many1_skip(), item(' ')).to(()),
                    tag("```").to(()),
                    tag("---").to(()),
                    item('>').to(()),
                    tag("- ").to(()),
                    (one_of("0123456789").many1_skip(), item('.'), item(' ')).to(()),
                )))
                .is_some()
            {
                return Some((end, trivia));
            }
            None
        }),
    );
    let ((), (end, trivia)) = match many_result {
        Some(r) => r,
        None => return None,
    };
    let text: Box<str> = I::seq(start, end).as_ref().into();
    let nud = match trivia.info() {
        crate::lex::TriviaInfo::None => {
            if text.is_empty() && !i.env.inline {
                // ドキュメント先頭 (改行前置なし): ブロック sigil を試してからインライン
                let block = i.maybe(from_fn(|mut i: In<I, S>| {
                    let ((kind, block_tag), t) = i.with_seq(choice((
                        tag("---").to((SyntaxKind::YmDocBlockSigil, BlockNudTag::DocBlockClose)),
                        tag("```").to((SyntaxKind::YmFenceSigil, BlockNudTag::Fence)),
                        (item('#').many1_skip(), item(' '))
                            .to((SyntaxKind::YmHashSigil, BlockNudTag::Heading)),
                        from_fn(scan_chevron_nud),
                        tag("- ").to((SyntaxKind::YmListDashSigil, BlockNudTag::ListMinus)),
                        from_fn(scan_list_num)
                            .to((SyntaxKind::YmListNumSigil, BlockNudTag::ListNum)),
                    )))?;
                    Some(MarkNud {
                        lex: Some(SyntaxLex {
                            text: t.as_ref().into(),
                            kind,
                        }),
                        tag: MarkNudTag::Block(block_tag),
                    })
                }))?;
                match block {
                    Some(nud) => nud,
                    None => scan_inline_nud(i)?,
                }
            } else {
                scan_inline_nud(i)?
            }
        }
        crate::lex::TriviaInfo::Space => scan_inline_nud(i)?,
        crate::lex::TriviaInfo::Newline {
            indent,
            quote_level,
            blank_line,
        } => {
            if blank_line && quote_level < i.env.mark_quote_depth {
                MarkNud {
                    lex: None,
                    tag: MarkNudTag::Block(BlockNudTag::Dequote {
                        quote_level,
                        indent,
                    }),
                }
            } else if blank_line {
                MarkNud {
                    lex: None,
                    tag: MarkNudTag::Block(BlockNudTag::NewParagraph),
                }
            } else if quote_level < i.env.mark_quote_depth {
                MarkNud {
                    lex: None,
                    tag: MarkNudTag::Block(BlockNudTag::Dequote {
                        quote_level,
                        indent,
                    }),
                }
            } else if i.env.inline {
                MarkNud {
                    lex: None,
                    tag: MarkNudTag::Block(BlockNudTag::LineEnd),
                }
            } else {
                scan_block_nud(i, indent)?
            }
        }
    };
    Some(Mark { text, trivia, nud })
}

fn scan_block_nud<I: EventInput, S: EventSink>(mut i: In<I, S>, indent: usize) -> Option<MarkNud> {
    let block = i.maybe(from_fn(|mut i: In<I, S>| {
        let ((kind, tag), text) = i.with_seq(choice((
            tag("---").to((SyntaxKind::YmDocBlockSigil, BlockNudTag::DocBlockClose)),
            tag("```").to((SyntaxKind::YmFenceSigil, BlockNudTag::Fence)),
            (item('#').many1_skip(), item(' ')).to((SyntaxKind::YmHashSigil, BlockNudTag::Heading)),
            from_fn(scan_chevron_nud),
            tag("- ").to((SyntaxKind::YmListDashSigil, BlockNudTag::ListMinus)),
            from_fn(scan_list_num).to((SyntaxKind::YmListNumSigil, BlockNudTag::ListNum)),
        )))?;
        Some(MarkNud {
            lex: Some(SyntaxLex {
                text: text.as_ref().into(),
                kind,
            }),
            tag: MarkNudTag::Block(tag),
        })
    }))?;
    Some(block.unwrap_or(MarkNud {
        lex: None,
        tag: MarkNudTag::Inline(InlineNudTag::Newline { indent }),
    }))
}

fn scan_chevron_nud<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
) -> Option<(SyntaxKind, BlockNudTag)> {
    i.skip(item('>'))?;
    let _ = i.maybe(one_of(" \t"))?;
    Some((SyntaxKind::YmChevronPrefixSigil, BlockNudTag::BlockQuote))
}

fn scan_list_num<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<()> {
    i.many1_skip(one_of("0123456789"))?;
    i.skip(item('.'))?;
    i.skip(item(' '))?;
    Some(())
}

fn scan_inline_nud<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<MarkNud> {
    if i.maybe(eoi)?.is_some() {
        return Some(MarkNud {
            lex: None,
            tag: MarkNudTag::Block(BlockNudTag::InputEnd),
        });
    }

    let ((kind, tag), text) = i.with_seq(choice((
        (item('#').many1_skip(), item('.'))
            .to((SyntaxKind::YmHashDotSigil, InlineNudTag::SectionClose)),
        tag("**").to((SyntaxKind::YmStrongSigil, InlineNudTag::Strong)),
        item('*').to((SyntaxKind::YmStarSigil, InlineNudTag::Emphasis)),
        item('!').to((SyntaxKind::YmBang, InlineNudTag::Bang)),
        item('[').to((SyntaxKind::BracketL, InlineNudTag::OpenBracket)),
        item('\\').to((SyntaxKind::YmBackslash, InlineNudTag::Backslash)),
        item(']').to((SyntaxKind::BracketR, InlineNudTag::CloseBracket)),
        item('}').to((SyntaxKind::BraceR, InlineNudTag::CloseBrace)),
    )))?;
    Some(MarkNud {
        lex: Some(SyntaxLex {
            text: text.as_ref().into(),
            kind,
        }),
        tag: MarkNudTag::Inline(tag),
    })
}
