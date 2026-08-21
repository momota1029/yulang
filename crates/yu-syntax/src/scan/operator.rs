//! NUD/LED-aware matching against the parse-session operator trie.

use std::ops::Range;

use chasa::{
    ErrorSink,
    error::std::{Unexpected, UnexpectedEndOfInput},
    parser::{SkipParserOnce as _, trie::TrieState as _},
    prelude::{from_fn, one_of},
};
use unicode_ident::{is_xid_continue, is_xid_start};

use crate::{
    operator::{
        BindingPower, OperatorEntry, OperatorFixities, OperatorFixity, OperatorKindSet,
        OperatorTable,
    },
    session::{StopKind, SynIn},
};

use super::trivia::{TriviaRun, scan_trivia};

/// One accepted operator use and its exact source extent.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ScannedOperator<'source> {
    text: &'source str,
    start: usize,
    end: usize,
    fixity: ScannedFixity,
    trailing_trivia: TriviaRun,
}

impl<'source> ScannedOperator<'source> {
    pub(crate) fn text(&self) -> &'source str {
        self.text
    }

    pub(crate) fn range(&self) -> Range<usize> {
        self.start..self.end
    }

    pub(crate) fn fixity(&self) -> &ScannedFixity {
        &self.fixity
    }

    pub(crate) fn trailing_trivia(&self) -> &TriviaRun {
        &self.trailing_trivia
    }
}

/// The selected fixity together with the binding power needed by Pratt parsing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ScannedFixity {
    Prefix {
        right: BindingPower,
    },
    Infix {
        left: BindingPower,
        right: BindingPower,
    },
    Suffix {
        left: BindingPower,
    },
    Nullfix,
}

impl ScannedFixity {
    pub(crate) fn kind(&self) -> OperatorFixity {
        match self {
            Self::Prefix { .. } => OperatorFixity::Prefix,
            Self::Infix { .. } => OperatorFixity::Infix,
            Self::Suffix { .. } => OperatorFixity::Suffix,
            Self::Nullfix => OperatorFixity::Nullfix,
        }
    }
}

/// Which side of a Pratt operand is requesting an operator.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum OperatorSite {
    Nud,
    Led,
}

/// Whether trivia separated this operator from the preceding token.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum LeadingTrivia {
    None,
    Present,
}

/// Matches the longest operator candidate accepted at the requested Pratt site.
///
/// The extra `leading` argument corresponds to the oracle's `TriviaInfo`: the
/// judge table only needs to know whether preceding trivia exists. Trailing
/// trivia is scanned here because its presence and indentation participate in
/// candidate acceptance.
pub(crate) fn scan_operator<'source, E>(
    site: OperatorSite,
    leading: LeadingTrivia,
    table: &OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<ScannedOperator<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let parser = table.state().longest_match_then(
        |last_character, entry: &OperatorEntry, mut candidate_input| {
            operator_boundary(last_character, &mut candidate_input)?;
            let end = candidate_input.pos();

            let mut line = candidate_input.local.line();
            line.at_line_start = false;
            candidate_input.local.set_line(line);

            let trailing_trivia = candidate_input.run(scan_trivia)?;
            let trailing = trailing_info(&trailing_trivia, candidate_input.local.line());
            let kinds = entry.fixities().kinds();

            if is_call_or_path_sensitive(kinds)
                && trailing == TrailingInfo::None
                && candidate_input.lookahead(one_of("(:").skip()).is_some()
            {
                return None;
            }

            let post_whitespace = trailing != TrailingInfo::None
                || candidate_input.input.remainder().is_empty()
                || next_is_expression_stop(&candidate_input);
            let pre_whitespace = leading == LeadingTrivia::Present;
            let with_value = judge(site, kinds, pre_whitespace, post_whitespace, true);
            let without_value = judge(site, kinds, pre_whitespace, post_whitespace, false);

            let fixity = if should_prefer_prefix_with_argument(kinds, post_whitespace)
                && candidate_input
                    .lookahead(from_fn(|probe| value_start(table, trailing, probe)))
                    .is_some()
            {
                Some(OperatorFixity::Prefix)
            } else if with_value != without_value {
                if candidate_input
                    .lookahead(from_fn(|probe| value_start(table, trailing, probe)))
                    .is_some()
                {
                    with_value
                } else {
                    without_value
                }
            } else {
                with_value
            }?;

            Some(AcceptedCandidate {
                end,
                fixity: scanned_fixity(entry.fixities(), fixity)?,
                trailing_trivia,
            })
        },
    );
    let accepted = i.maybe(parser)??;

    Some(ScannedOperator {
        text: &i.input.source()[start..accepted.end],
        start,
        end: accepted.end,
        fixity: accepted.fixity,
        trailing_trivia: accepted.trailing_trivia,
    })
}

struct AcceptedCandidate {
    end: usize,
    fixity: ScannedFixity,
    trailing_trivia: TriviaRun,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TrailingInfo {
    None,
    Space,
    Newline { indentation: usize },
}

fn trailing_info(run: &TriviaRun, line: crate::session::LineState) -> TrailingInfo {
    if run.is_empty() {
        return TrailingInfo::None;
    }
    let range = run.range();
    if line
        .last_newline
        .is_some_and(|(start, end)| range.contains(&start) && end <= range.end)
    {
        TrailingInfo::Newline {
            indentation: line.line_indent,
        }
    } else {
        TrailingInfo::Space
    }
}

fn operator_boundary<E>(
    last_character: char,
    i: &mut SynIn<E>,
) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    if is_xid_continue(last_character) {
        i.not(one_of(is_xid_continue))
    } else {
        Some(())
    }
}

fn value_start<E>(
    table: &OperatorTable,
    trailing: TrailingInfo,
    mut i: SynIn<E>,
) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    if let TrailingInfo::Newline { indentation } = trailing {
        let baseline = i
            .local
            .indentation_baseline()
            .map_or(0, |baseline| baseline.column);
        (baseline < indentation).then_some(())?;
    }

    i.choice((
        one_of("\"([{$\\").to(()),
        one_of("$%_'").to(()),
        one_of(is_xid_start).to(()),
        one_of(|character: char| character.is_ascii_digit()).to(()),
        one_of(".").to(()),
        from_fn(|probe| operator_value_start(table, probe)),
    ))
}

fn operator_value_start<E>(
    table: &OperatorTable,
    mut i: SynIn<E>,
) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let parser = table.state().longest_match_then(
        |last_character, entry: &OperatorEntry, mut candidate_input| {
            operator_boundary(last_character, &mut candidate_input)?;
            entry
                .fixities()
                .kinds()
                .contains(OperatorKindSet::PREFIX | OperatorKindSet::NULLFIX)
                .then_some(())
        },
    );
    i.run(parser)
}

fn next_is_expression_stop<E>(i: &SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
{
    let Some(stops) = i.local.stop_set() else {
        return false;
    };
    match i.input.remainder().chars().next() {
        Some(',') => stops.contains(StopKind::Comma),
        Some(')') => stops.contains(StopKind::RightParenthesis),
        Some(']') => stops.contains(StopKind::RightBracket),
        Some('}') => stops.contains(StopKind::RightBrace),
        _ => false,
    }
}

fn is_call_or_path_sensitive(kinds: OperatorKindSet) -> bool {
    kinds.contains(OperatorKindSet::PREFIX | OperatorKindSet::NULLFIX)
        && !kinds.contains(OperatorKindSet::INFIX)
        && !kinds.contains(OperatorKindSet::SUFFIX)
}

fn should_prefer_prefix_with_argument(kinds: OperatorKindSet, post_whitespace: bool) -> bool {
    post_whitespace && is_call_or_path_sensitive(kinds)
}

fn scanned_fixity(fixities: &OperatorFixities, fixity: OperatorFixity) -> Option<ScannedFixity> {
    match fixity {
        OperatorFixity::Prefix => Some(ScannedFixity::Prefix {
            right: fixities.prefix()?.right_binding_power().clone(),
        }),
        OperatorFixity::Infix => {
            let infix = fixities.infix()?;
            Some(ScannedFixity::Infix {
                left: infix.left_binding_power().clone(),
                right: infix.right_binding_power().clone(),
            })
        }
        OperatorFixity::Suffix => Some(ScannedFixity::Suffix {
            left: fixities.suffix()?.left_binding_power().clone(),
        }),
        OperatorFixity::Nullfix => fixities.is_nullfix().then_some(ScannedFixity::Nullfix),
    }
}

fn judge(
    site: OperatorSite,
    kinds: OperatorKindSet,
    pre_whitespace: bool,
    post_whitespace: bool,
    probe_value_start: bool,
) -> Option<OperatorFixity> {
    match site {
        OperatorSite::Nud => judge_nud(
            kind_bits(kinds),
            pre_whitespace,
            post_whitespace,
            probe_value_start,
        ),
        OperatorSite::Led => judge_led(
            kind_bits(kinds),
            pre_whitespace,
            post_whitespace,
            probe_value_start,
        ),
    }
}

const PREFIX: u8 = 1 << 0;
const INFIX: u8 = 1 << 1;
const SUFFIX: u8 = 1 << 2;
const NULLFIX: u8 = 1 << 3;

fn kind_bits(kinds: OperatorKindSet) -> u8 {
    let mut bits = 0;
    for (kind, bit) in [
        (OperatorKindSet::PREFIX, PREFIX),
        (OperatorKindSet::INFIX, INFIX),
        (OperatorKindSet::SUFFIX, SUFFIX),
        (OperatorKindSet::NULLFIX, NULLFIX),
    ] {
        if kinds.contains(kind) {
            bits |= bit;
        }
    }
    bits
}

fn judge_nud(
    mut kinds: u8,
    pre_whitespace: bool,
    post_whitespace: bool,
    probe_value_start: bool,
) -> Option<OperatorFixity> {
    kinds &= !(INFIX | SUFFIX);
    if !probe_value_start {
        kinds &= !PREFIX;
    }
    judge_table(kinds, pre_whitespace, post_whitespace)
}

fn judge_led(
    mut kinds: u8,
    pre_whitespace: bool,
    post_whitespace: bool,
    probe_value_start: bool,
) -> Option<OperatorFixity> {
    if !probe_value_start {
        kinds &= !(PREFIX | INFIX);
    }
    let mut multiline_argument_kinds = kinds;
    if post_whitespace {
        multiline_argument_kinds &= !PREFIX;
    }
    judge_table(multiline_argument_kinds, pre_whitespace, post_whitespace)
        .or_else(|| judge_table(kinds, pre_whitespace, post_whitespace))
}

fn judge_table(kinds: u8, pre_whitespace: bool, post_whitespace: bool) -> Option<OperatorFixity> {
    use OperatorFixity::{Infix, Nullfix, Prefix, Suffix};

    const P: Option<OperatorFixity> = Some(Prefix);
    const I: Option<OperatorFixity> = Some(Infix);
    const S: Option<OperatorFixity> = Some(Suffix);
    const N: Option<OperatorFixity> = Some(Nullfix);
    const X: Option<OperatorFixity> = None;
    const TABLE: [[Option<OperatorFixity>; 4]; 16] = [
        [X, X, X, X],
        [P, P, P, P],
        [I, I, I, I],
        [I, I, P, I],
        [S, S, S, S],
        [X, S, P, X],
        [I, S, I, I],
        [I, S, P, I],
        [N, N, N, N],
        [P, N, P, N],
        [I, I, I, N],
        [I, I, P, N],
        [N, S, N, N],
        [N, S, P, N],
        [I, S, I, N],
        [I, S, P, N],
    ];
    let whitespace = ((pre_whitespace as usize) << 1) | post_whitespace as usize;
    TABLE[kinds as usize][whitespace]
}

#[cfg(test)]
mod tests {
    use super::*;
    use chasa::{input::IsCut, prelude::In};

    use crate::{
        input::SourceInput,
        operator::{OperatorDeclaration, OperatorFixities},
        session::{Delimiter, EmbeddedLexicalMode, LineState, ParseLocal},
    };

    #[test]
    fn nud_falls_back_to_short_prefix_while_led_keeps_long_infix() {
        let plus_right = BindingPower::scalar(70);
        let bang_right = BindingPower::scalar(80);
        let long_left = BindingPower::scalar(50);
        let long_right = BindingPower::new(50, [1]);
        let table = OperatorTable::from_declarations([
            OperatorDeclaration::new(
                "+!",
                OperatorFixities::new().with_infix(long_left.clone(), long_right.clone()),
            ),
            OperatorDeclaration::new("+", OperatorFixities::new().with_prefix(plus_right.clone())),
            // Operator value-start requires both bits, while the accepted use
            // before `a` is still Prefix.
            OperatorDeclaration::new(
                "!",
                OperatorFixities::new()
                    .with_prefix(bang_right.clone())
                    .with_nullfix(),
            ),
        ])
        .expect("canonical operator table should build");

        let mut nud_source = SourceInput::new("+!a");
        let mut nud_local = ParseLocal::new();
        nud_local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        nud_local.push_delimiter(Delimiter::Brace);
        nud_local.push_lexical_mode(EmbeddedLexicalMode::RuleLiteral);
        let mut nud_expectations = chasa::LatestSink::new();
        let mut nud_cut = false;
        let mut nud_input = In::new(
            &mut nud_source,
            &mut nud_expectations,
            IsCut::new(&mut nud_cut),
        )
        .set_local(&mut nud_local);

        let plus = nud_input
            .run(from_fn(|i| {
                scan_operator(OperatorSite::Nud, LeadingTrivia::None, &table, i)
            }))
            .expect("NUD should fall back to the short plus");
        assert_eq!(plus.text(), "+");
        assert_eq!(plus.range(), 0..1);
        assert_eq!(
            plus.fixity(),
            &ScannedFixity::Prefix {
                right: plus_right.clone()
            }
        );
        assert_eq!(nud_input.input.remainder(), "!a");

        let bang = nud_input
            .run(from_fn(|i| {
                scan_operator(OperatorSite::Nud, LeadingTrivia::None, &table, i)
            }))
            .expect("recursive NUD should accept bang as prefix");
        assert_eq!(bang.text(), "!");
        assert_eq!(bang.range(), 1..2);
        assert_eq!(bang.fixity(), &ScannedFixity::Prefix { right: bang_right });
        assert_eq!(nud_input.input.remainder(), "a");
        assert_eq!(nud_input.local.delimiter(), Some(Delimiter::Brace));
        assert_eq!(
            nud_input.local.lexical_mode(),
            Some(EmbeddedLexicalMode::RuleLiteral)
        );
        assert!(!nud_input.local.line().at_line_start);

        let mut led_source = SourceInput::new("+!b");
        let mut led_local = ParseLocal::new();
        let mut led_expectations = chasa::LatestSink::new();
        let mut led_cut = false;
        let mut led_input = In::new(
            &mut led_source,
            &mut led_expectations,
            IsCut::new(&mut led_cut),
        )
        .set_local(&mut led_local);

        let long = led_input
            .run(from_fn(|i| {
                scan_operator(OperatorSite::Led, LeadingTrivia::None, &table, i)
            }))
            .expect("LED should accept the longest infix candidate");
        assert_eq!(long.text(), "+!");
        assert_eq!(long.range(), 0..2);
        assert_eq!(
            long.fixity(),
            &ScannedFixity::Infix {
                left: long_left,
                right: long_right,
            }
        );
        assert_eq!(led_input.input.remainder(), "b");
    }

    #[test]
    fn site_mismatch_returns_none_without_mutating_input_or_local_stacks() {
        let table = OperatorTable::from_declarations([OperatorDeclaration::new(
            "@",
            OperatorFixities::new()
                .with_infix(BindingPower::scalar(40), BindingPower::new(40, [1])),
        )])
        .expect("infix-only table should build");
        let original_line = LineState {
            last_newline: Some((2, 3)),
            line_start: 3,
            line_indent: 2,
            at_line_start: true,
        };
        let mut source = SourceInput::new("@value");
        let mut local = ParseLocal::new();
        local.set_line(original_line);
        local.push_delimiter(Delimiter::Parenthesis);
        local.push_lexical_mode(EmbeddedLexicalMode::BlockComment { depth: 2 });
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i =
            In::new(&mut source, &mut expectations, IsCut::new(&mut is_cut)).set_local(&mut local);

        let scanned = i.run(from_fn(|i| {
            scan_operator(OperatorSite::Nud, LeadingTrivia::None, &table, i)
        }));

        assert_eq!(scanned, None);
        assert_eq!(i.pos(), 0);
        assert_eq!(i.input.remainder(), "@value");
        assert_eq!(i.local.line(), original_line);
        assert_eq!(i.local.delimiter(), Some(Delimiter::Parenthesis));
        assert_eq!(
            i.local.lexical_mode(),
            Some(EmbeddedLexicalMode::BlockComment { depth: 2 })
        );
    }

    #[test]
    fn operator_value_start_keeps_prefix_and_nullfix_and_semantics() {
        let table = OperatorTable::from_declarations([
            OperatorDeclaration::new(
                "+",
                OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
            ),
            OperatorDeclaration::new(
                "!",
                OperatorFixities::new().with_prefix(BindingPower::scalar(80)),
            ),
        ])
        .expect("prefix-only table should build");
        let mut source = SourceInput::new("+!a");
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i =
            In::new(&mut source, &mut expectations, IsCut::new(&mut is_cut)).set_local(&mut local);

        let scanned = i.run(from_fn(|i| {
            scan_operator(OperatorSite::Nud, LeadingTrivia::None, &table, i)
        }));

        assert_eq!(scanned, None);
        assert_eq!(i.pos(), 0);
        assert_eq!(i.input.remainder(), "+!a");
    }

    #[test]
    fn rejected_long_candidate_rolls_back_trailing_newline_state() {
        let table = OperatorTable::from_declarations([
            OperatorDeclaration::new(
                "+!",
                OperatorFixities::new()
                    .with_infix(BindingPower::scalar(50), BindingPower::new(50, [1])),
            ),
            OperatorDeclaration::new(
                "+",
                OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
            ),
            OperatorDeclaration::new(
                "!",
                OperatorFixities::new()
                    .with_prefix(BindingPower::scalar(80))
                    .with_nullfix(),
            ),
        ])
        .expect("canonical operator table should build");
        let original_line = LineState {
            last_newline: Some((12, 13)),
            line_start: 13,
            line_indent: 4,
            at_line_start: true,
        };
        let mut source = SourceInput::new("+!\n  a");
        let mut local = ParseLocal::new();
        local.set_line(original_line);
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i =
            In::new(&mut source, &mut expectations, IsCut::new(&mut is_cut)).set_local(&mut local);

        let plus = i
            .run(from_fn(|i| {
                scan_operator(OperatorSite::Nud, LeadingTrivia::None, &table, i)
            }))
            .expect("short prefix should survive rejected long candidate");

        assert_eq!(plus.text(), "+");
        assert_eq!(plus.trailing_trivia().range(), 1..1);
        assert_eq!(i.input.remainder(), "!\n  a");
        assert_eq!(
            i.local.line(),
            LineState {
                at_line_start: false,
                ..original_line
            }
        );
    }
}
