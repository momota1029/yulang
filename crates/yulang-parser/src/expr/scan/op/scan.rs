use chasa::Back as _;
use chasa::parser::SkipParserOnce as _;
use chasa::parser::trie::TrieState as ChasaTrieState;
use chasa::prelude::{cut_on_ok, eoi, from_fn, one_of};
use reborrow_generic::Reborrow as _;
use unicode_ident::is_xid_start;

use crate::EventInput;
use crate::context;
use crate::expr::scan::op::boundary::boundary;
use crate::expr::scan::op::judge::{judge_led, judge_nud};
use crate::lex::{Lex, SyntaxKind, TriviaInfo};
use crate::op::{OpDef, OpKindSet, OpUse};
use crate::scan::scan_punct_expr;
use crate::scan::trivia::scan_trivia;
use crate::sink::EventSink;

pub fn scan_op_nud<I: EventInput, S: EventSink>(
    i: context::In<I, S>,
    leading_info: TriviaInfo,
) -> Option<(OpUse, OpDef, Lex)> {
    scan_op_with_trie(i, leading_info, judge_nud)
}

pub fn scan_op_led<I: EventInput, S: EventSink>(
    i: context::In<I, S>,
    leading_info: TriviaInfo,
) -> Option<(OpUse, OpDef, Lex)> {
    scan_op_with_trie(i, leading_info, judge_led)
}

fn scan_op_with_trie<I: EventInput, S: EventSink, F>(
    mut i: context::In<I, S>,
    leading_info: TriviaInfo,
    judge: F,
) -> Option<(OpUse, OpDef, Lex)>
where
    F: Fn(OpKindSet, bool, bool, bool) -> Option<OpUse> + Copy,
{
    let start_cp = i.checkpoint().input;
    let ops = i.env.state.ops.clone();
    let trie = ops.state();

    let parser = trie.longest_match_then(|last_char, def: OpDef, mut i: context::In<I, S>| {
        boundary(last_char, i.rb())?;
        let end_cp = i.checkpoint().input;

        let pre_ws = !matches!(leading_info, TriviaInfo::None);

        let trailing_trivia = scan_trivia(i.rb())?;
        let post_info = trailing_trivia.info();
        let text = I::seq(start_cp.clone(), end_cp.clone());
        if is_call_or_path_sensitive_operator(def.kinds())
            && matches!(post_info, TriviaInfo::None)
            && i.lookahead(one_of("(:").skip()).is_some()
        {
            return None;
        }
        if is_loop_control_op(text.as_ref()) {
            if matches!(post_info, TriviaInfo::Space)
                && i.lookahead(one_of("'").skip()).is_none()
                && i.lookahead(from_fn(|i| value_start(i, &post_info)))
                    .is_some()
            {
                return None;
            }
        }
        let is_eof = i.maybe(eoi)?.is_some();
        let post_ws = !matches!(post_info, TriviaInfo::None) || is_eof || next_is_expr_stop(i.rb());

        let a = judge(def.kinds(), pre_ws, post_ws, true);
        let b = judge(def.kinds(), pre_ws, post_ws, false);

        let use_ = if should_prefer_prefix_with_argument(def.kinds(), post_ws)
            && i.lookahead(from_fn(|i| value_start(i, &post_info)))
                .is_some()
        {
            Some(OpUse::Prefix)
        } else if a != b {
            let probe = i
                .lookahead(from_fn(|i| value_start(i, &post_info)))
                .is_some();
            if probe { a } else { b }
        } else {
            a
        }?;

        Some((use_, def, end_cp, trailing_trivia))
    });

    let (use_, def, end_cp, trailing_trivia) = i.run(cut_on_ok(parser))?;

    let text: Box<str> = I::seq(start_cp, end_cp).as_ref().into();
    let kind = match use_ {
        OpUse::Prefix => {
            def.prefix.as_ref()?;
            SyntaxKind::Prefix
        }
        OpUse::Infix => {
            def.infix.as_ref()?;
            SyntaxKind::Infix
        }
        OpUse::Suffix => {
            def.suffix.as_ref()?;
            SyntaxKind::Suffix
        }
        OpUse::Nullfix => SyntaxKind::Nullfix,
    };

    let lex = Lex {
        leading_trivia_info: leading_info,
        kind,
        text,
        trailing_trivia,
    };

    Some((use_, def, lex))
}

fn is_call_or_path_sensitive_operator(kinds: OpKindSet) -> bool {
    kinds.contains(OpKindSet::PREFIX)
        && kinds.contains(OpKindSet::NULLFIX)
        && !kinds.contains(OpKindSet::INFIX)
        && !kinds.contains(OpKindSet::SUFFIX)
}

fn should_prefer_prefix_with_argument(kinds: OpKindSet, post_ws: bool) -> bool {
    post_ws && is_call_or_path_sensitive_operator(kinds)
}

fn is_loop_control_op(text: &str) -> bool {
    matches!(text, "last" | "next" | "redo")
}

fn next_is_expr_stop<I: EventInput, S: EventSink>(mut i: context::In<I, S>) -> bool {
    i.lookahead(from_fn(|mut i: context::In<I, S>| {
        let (kind, _) = scan_punct_expr(i.rb())?;
        i.env.stop.contains(&kind).then_some(())
    }))
    .is_some()
}

fn value_start<I: EventInput, S: EventSink>(
    mut i: context::In<I, S>,
    trivia_info: &TriviaInfo,
) -> Option<()> {
    if let TriviaInfo::Newline { indent, .. } = trivia_info {
        i.when(i.env.indent < *indent)?;
    }

    let string_or_group = one_of("\"([{$\\").skip();
    let sigil = one_of("$%_").skip();
    let ident_start = one_of(is_xid_start).skip();
    let digit = one_of(|c: char| c.is_ascii_digit()).skip();
    let dot = one_of(".").skip();

    i.choice((
        string_or_group,
        sigil,
        ident_start,
        digit,
        dot,
        op_value_start_inner,
    ))
}

fn op_value_start_inner<I: EventInput, S: EventSink>(mut i: context::In<I, S>) -> Option<()> {
    let ops = i.env.state.ops.clone();
    let trie = ops.state();

    let parser = trie.longest_match_then(|last_char, def: OpDef, mut i: context::In<I, S>| {
        boundary(last_char, i.rb())?;
        let kinds = def.kinds();
        if kinds.contains(OpKindSet::PREFIX | OpKindSet::NULLFIX) {
            Some(())
        } else {
            None
        }
    });

    i.run(cut_on_ok(parser))
}
