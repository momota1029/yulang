//! Source-only physical trivia observation without Item or CST construction.

use crate::lexical::current_item::LineEntry;
use crate::lexical::yumark::FenceBoundary;
use crate::lexical::yumark::FenceLineDecision;
use crate::lexical::yumark::judge_fence_line;

pub(crate) fn lone_colon_after_fenced_trivia(
    source: &str,
    source_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> bool {
    matches!(
        observe_fenced_trivia(source, source_origin, line_entry, fence),
        TriviaObservation::Visible(VisibleTrivia { source, .. })
            if source.starts_with(':') && !source.starts_with("::")
    )
}

pub(crate) fn newline_indentation_after_fenced_trivia(
    source: &str,
    source_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> Option<usize> {
    match observe_fenced_trivia(source, source_origin, line_entry, fence) {
        TriviaObservation::Visible(visible) => visible.indentation,
        TriviaObservation::Boundary => None,
    }
}

pub(crate) enum TriviaObservation<'source> {
    Visible(VisibleTrivia<'source>),
    Boundary,
}

pub(crate) struct VisibleTrivia<'source> {
    pub(crate) source: &'source str,
    pub(crate) present: bool,
    pub(crate) indentation: Option<usize>,
}

pub(crate) struct TriviaObservationWithNewline<'source> {
    pub(crate) observation: TriviaObservation<'source>,
    pub(crate) saw_physical_newline: bool,
}

/// Reads one maximal trivia suffix without building Items or fence facts.
/// Under a fence it stops at the first close, transition, or physical EOF and
/// never reads the next outer line. Accepted quote prefixes are skipped as
/// foreign physical text, never reclassified as ordinary whitespace.
pub(crate) fn observe_fenced_trivia<'source>(
    source: &'source str,
    source_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> TriviaObservation<'source> {
    observe_fenced_trivia_with_newline(source, source_origin, line_entry, fence).observation
}

/// Fence-aware trivia observation with the physical-newline fact retained
/// even when the visible suffix ends at a close, transition, or physical EOF.
pub(crate) fn observe_fenced_trivia_with_newline<'source>(
    mut source: &'source str,
    mut source_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> TriviaObservationWithNewline<'source> {
    if fence.is_none() {
        let observation = observe_ordinary_trivia(source);
        let saw_physical_newline = matches!(
            &observation,
            TriviaObservation::Visible(visible) if visible.indentation.is_some()
        );
        return TriviaObservationWithNewline {
            observation,
            saw_physical_newline,
        };
    }

    let mut present = false;
    let mut saw_newline = false;
    let mut at_line_start = false;
    let mut indentation = 0usize;

    if !observe_line(
        &mut source,
        &mut source_origin,
        &mut line_entry,
        fence,
        &mut at_line_start,
    ) {
        return TriviaObservationWithNewline {
            observation: TriviaObservation::Boundary,
            saw_physical_newline: saw_newline,
        };
    }

    loop {
        if source.starts_with([' ', '\t']) {
            present = true;
            let character = source
                .chars()
                .next()
                .expect("a nonempty source suffix has one character");
            raw_trivia_character(
                character,
                &mut saw_newline,
                &mut at_line_start,
                &mut indentation,
            );
            advance_source(&mut source, &mut source_origin, character.len_utf8());
            continue;
        }

        if source.starts_with("\r\n") {
            present = true;
            raw_trivia_character('\r', &mut saw_newline, &mut at_line_start, &mut indentation);
            raw_trivia_character('\n', &mut saw_newline, &mut at_line_start, &mut indentation);
            advance_source(&mut source, &mut source_origin, 2);
            line_entry = LineEntry::PhysicalStart;
            if !observe_line(
                &mut source,
                &mut source_origin,
                &mut line_entry,
                fence,
                &mut at_line_start,
            ) {
                return TriviaObservationWithNewline {
                    observation: TriviaObservation::Boundary,
                    saw_physical_newline: saw_newline,
                };
            }
            continue;
        }

        if source.starts_with('\n') {
            present = true;
            raw_trivia_character('\n', &mut saw_newline, &mut at_line_start, &mut indentation);
            advance_source(&mut source, &mut source_origin, 1);
            line_entry = LineEntry::PhysicalStart;
            if !observe_line(
                &mut source,
                &mut source_origin,
                &mut line_entry,
                fence,
                &mut at_line_start,
            ) {
                return TriviaObservationWithNewline {
                    observation: TriviaObservation::Boundary,
                    saw_physical_newline: saw_newline,
                };
            }
            continue;
        }

        if source.starts_with('\r') {
            present = true;
            raw_trivia_character('\r', &mut saw_newline, &mut at_line_start, &mut indentation);
            advance_source(&mut source, &mut source_origin, 1);
            line_entry = LineEntry::InLine;
            continue;
        }

        if source.starts_with("//") {
            present = true;
            raw_trivia_character('/', &mut saw_newline, &mut at_line_start, &mut indentation);
            raw_trivia_character('/', &mut saw_newline, &mut at_line_start, &mut indentation);
            advance_source(&mut source, &mut source_origin, 2);
            while let Some(character) = source.chars().next() {
                if matches!(character, '\r' | '\n') {
                    break;
                }
                raw_trivia_character(
                    character,
                    &mut saw_newline,
                    &mut at_line_start,
                    &mut indentation,
                );
                advance_source(&mut source, &mut source_origin, character.len_utf8());
            }
            continue;
        }

        if source.starts_with("/*") {
            present = true;
            if !observe_block_comment(
                &mut source,
                &mut source_origin,
                &mut line_entry,
                fence,
                &mut saw_newline,
                &mut at_line_start,
                &mut indentation,
            ) {
                return TriviaObservationWithNewline {
                    observation: TriviaObservation::Boundary,
                    saw_physical_newline: saw_newline,
                };
            }
            continue;
        }

        if source.is_empty() && fence.is_some() {
            return TriviaObservationWithNewline {
                observation: TriviaObservation::Boundary,
                saw_physical_newline: saw_newline,
            };
        }

        return TriviaObservationWithNewline {
            observation: TriviaObservation::Visible(VisibleTrivia {
                source,
                present,
                indentation: saw_newline.then_some(indentation),
            }),
            saw_physical_newline: saw_newline,
        };
    }
}

/// The `None` mode is the retained ordinary raw scanner. It deliberately
/// avoids fence coordinates and line classification, preserving the ordinary
/// operator/follower path's work and result shape.
fn observe_ordinary_trivia<'source>(mut source: &'source str) -> TriviaObservation<'source> {
    let mut present = false;
    let mut saw_newline = false;
    let mut at_line_start = false;
    let mut indentation = 0usize;

    loop {
        let before = source;
        while let Some(character) = source.chars().next() {
            if !matches!(character, ' ' | '\t' | '\r' | '\n') {
                break;
            }
            present = true;
            raw_trivia_character(
                character,
                &mut saw_newline,
                &mut at_line_start,
                &mut indentation,
            );
            source = &source[character.len_utf8()..];
        }
        if source.starts_with("//") {
            present = true;
            source = &source[2..];
            raw_trivia_character('/', &mut saw_newline, &mut at_line_start, &mut indentation);
            raw_trivia_character('/', &mut saw_newline, &mut at_line_start, &mut indentation);
            while let Some(character) = source.chars().next() {
                if matches!(character, '\r' | '\n') {
                    break;
                }
                raw_trivia_character(
                    character,
                    &mut saw_newline,
                    &mut at_line_start,
                    &mut indentation,
                );
                source = &source[character.len_utf8()..];
            }
            continue;
        }
        if source.starts_with("/*") {
            present = true;
            let comment = source;
            source = ordinary_block_comment_suffix(source);
            let consumed = comment.len() - source.len();
            for character in comment[..consumed].chars() {
                raw_trivia_character(
                    character,
                    &mut saw_newline,
                    &mut at_line_start,
                    &mut indentation,
                );
            }
            continue;
        }
        if source.len() == before.len() {
            return TriviaObservation::Visible(VisibleTrivia {
                source,
                present,
                indentation: saw_newline.then_some(indentation),
            });
        }
    }
}

fn ordinary_block_comment_suffix(mut source: &str) -> &str {
    debug_assert!(source.starts_with("/*"));
    source = &source[2..];
    let mut depth = 1usize;
    while !source.is_empty() {
        if source.starts_with("/*") {
            depth += 1;
            source = &source[2..];
            continue;
        }
        if source.starts_with("*/") {
            depth -= 1;
            source = &source[2..];
            if depth == 0 {
                return source;
            }
            continue;
        }
        let character = source
            .chars()
            .next()
            .expect("a nonempty UTF-8 suffix has one character");
        source = &source[character.len_utf8()..];
    }
    source
}

fn observe_line(
    source: &mut &str,
    source_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
    at_line_start: &mut bool,
) -> bool {
    if *line_entry != LineEntry::PhysicalStart {
        return true;
    }
    let Some(fence) = fence else {
        return true;
    };
    match judge_fence_line(source, *source_origin, fence) {
        FenceLineDecision::Boundary(_) => false,
        FenceLineDecision::Body { prefix: None, .. } => {
            *line_entry = LineEntry::InLine;
            true
        }
        FenceLineDecision::Body {
            prefix: Some(_),
            content,
        } => {
            let length = content
                .checked_sub(*source_origin)
                .expect("a judged source prefix remains on its current line");
            advance_source(source, source_origin, length);
            *line_entry = LineEntry::InLine;
            *at_line_start = true;
            true
        }
    }
}

fn observe_block_comment(
    source: &mut &str,
    source_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
    saw_newline: &mut bool,
    at_line_start: &mut bool,
    indentation: &mut usize,
) -> bool {
    debug_assert!(source.starts_with("/*"));
    raw_trivia_character('/', saw_newline, at_line_start, indentation);
    raw_trivia_character('*', saw_newline, at_line_start, indentation);
    advance_source(source, source_origin, 2);
    let mut depth = 1usize;

    while !source.is_empty() {
        if source.starts_with("/*") {
            raw_trivia_character('/', saw_newline, at_line_start, indentation);
            raw_trivia_character('*', saw_newline, at_line_start, indentation);
            advance_source(source, source_origin, 2);
            depth = depth
                .checked_add(1)
                .expect("block-comment depth must fit usize");
            continue;
        }
        if source.starts_with("*/") {
            raw_trivia_character('*', saw_newline, at_line_start, indentation);
            raw_trivia_character('/', saw_newline, at_line_start, indentation);
            advance_source(source, source_origin, 2);
            depth -= 1;
            if depth == 0 {
                return true;
            }
            continue;
        }
        if source.starts_with("\r\n") {
            raw_trivia_character('\r', saw_newline, at_line_start, indentation);
            raw_trivia_character('\n', saw_newline, at_line_start, indentation);
            advance_source(source, source_origin, 2);
            *line_entry = LineEntry::PhysicalStart;
            if !observe_line(source, source_origin, line_entry, fence, at_line_start) {
                return false;
            }
            continue;
        }
        if source.starts_with('\n') {
            raw_trivia_character('\n', saw_newline, at_line_start, indentation);
            advance_source(source, source_origin, 1);
            *line_entry = LineEntry::PhysicalStart;
            if !observe_line(source, source_origin, line_entry, fence, at_line_start) {
                return false;
            }
            continue;
        }
        let character = source
            .chars()
            .next()
            .expect("a nonempty source suffix has one character");
        raw_trivia_character(character, saw_newline, at_line_start, indentation);
        advance_source(source, source_origin, character.len_utf8());
    }
    true
}

fn advance_source(source: &mut &str, source_origin: &mut usize, length: usize) {
    *source = &source[length..];
    *source_origin = source_origin
        .checked_add(length)
        .expect("a source-only probe coordinate must fit usize");
}

fn raw_trivia_character(
    character: char,
    saw_newline: &mut bool,
    at_line_start: &mut bool,
    indentation: &mut usize,
) {
    match character {
        '\r' | '\n' => {
            *saw_newline = true;
            *at_line_start = true;
            *indentation = 0;
        }
        ' ' | '\t' if *at_line_start => *indentation += 1,
        _ => *at_line_start = false,
    }
}
