//! Direct, fence-normalized `use` declaration and recursive use-tree construction.

use reborrow_generic::Reborrow as _;
use unicode_ident::is_xid_continue;

use crate::cst_output::RecoveryDraft;
use crate::recovery_record::{
    ConstructRole, DeclarationRole, Delimiter, ExpectationSources, ExpectedSyntax, GrammarRole,
    ImportRole, PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation,
    UnexpectedCategory, UnexpectedSyntax,
};
use crate::{
    HeaderImport, HeaderImportForm, HeaderImportRoute, HeaderImportRouteSeparator, Visibility,
    syntax_kind::SyntaxKind,
};
use std::{ops::Range, sync::Arc};

use crate::{
    cst_output::emit::{emit_recovery_error_run, emit_recovery_missing},
    cursor::{LexIn, SyntaxIn},
    handoff::{NormalizedExit, complete, handoff},
    lexical::{
        current_item::{AcceptedPayload, CurrentItem, CurrentPayload, LineEntry, current_item},
        item::{Item, LeadingTrivia, Token, TokenKind},
        lexer::{
            scan_arm_arrow, scan_identifier, scan_punctuation, scan_unknown, source_identifier,
        },
        observation::{indentation_after_newline, token_kind},
        stops::Stops,
        trivia::{TriviaObservation, observe_fenced_trivia},
        yumark::FenceBoundary,
    },
};

/// Projection is collected by the grammar owner, with one temporary batch per
/// declaration. A failed branch invalidates the batch without retracting syntax.
#[derive(Default)]
struct Projection {
    frames: Vec<ImportFrame>,
    imports: Vec<HeaderImport>,
    invalid: bool,
    declaration_start: usize,
    visibility: Option<Visibility>,
    alias: bool,
    segments: Vec<String>,
    separators: Vec<HeaderImportRouteSeparator>,
}

struct ImportFrame {
    start: usize,
    form: HeaderImportForm,
    segment_base: usize,
    separator_base: usize,
    join: Option<HeaderImportRouteSeparator>,
    terminal: Terminal,
    aliases: Vec<String>,
}

impl Projection {
    fn begin(&mut self, start: usize) {
        let (form, join) = self
            .frames
            .last()
            .map_or((HeaderImportForm::Plain, None), |parent| {
                (parent.form, parent.join)
            });
        self.frames.push(ImportFrame {
            start,
            form,
            segment_base: self.segments.len(),
            separator_base: self.separators.len(),
            join,
            terminal: Terminal::Single,
            aliases: Vec::new(),
        });
    }

    fn form(&mut self, form: HeaderImportForm) {
        let frame = self.frames.last_mut().unwrap();
        if !self.segments.is_empty() {
            self.invalid = true;
        }
        frame.form = form;
    }

    fn segment(&mut self, text: &str) {
        let frame = self.frames.last_mut().unwrap();
        if self.alias {
            frame.aliases.push(text.to_owned());
            return;
        }
        if !self.segments.is_empty() {
            if let Some(join) = frame.join.take() {
                self.separators.push(join);
            } else {
                self.invalid = true;
            }
        }
        self.segments.push(text.to_owned());
    }

    fn separator(&mut self, separator: Separator) {
        self.frames.last_mut().unwrap().join = Some(match separator {
            Separator::ColonColon => HeaderImportRouteSeparator::ColonColon,
            Separator::Slash => HeaderImportRouteSeparator::Slash,
        });
    }

    fn finish(&mut self, end: usize) {
        let frame = self.frames.pop().unwrap();
        if frame.terminal != Terminal::Single {
            self.invalid |= !frame.aliases.is_empty();
        } else if self.segments.is_empty()
            || frame.join.is_some()
            || frame.aliases.len() > 1
            || self.separators.len() != self.segments.len().saturating_sub(1)
        {
            self.invalid = true;
        } else {
            let start = if self.frames.is_empty() {
                self.declaration_start
            } else {
                frame.start
            };
            self.imports.push(HeaderImport::new(
                start..end,
                frame.form,
                HeaderImportRoute::new(self.segments.clone(), self.separators.clone()),
                self.visibility.unwrap_or(Visibility::Private),
                frame.aliases.into_iter().next(),
            ));
        }
        self.segments.truncate(frame.segment_base);
        self.separators.truncate(frame.separator_base);
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn use_declaration_normalized(
    i: SyntaxIn,
    intro: Item,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    use_declaration_header_normalized(i, intro, baseline, stops, item_origin, line_entry, fence).0
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn use_declaration_header_normalized(
    i: SyntaxIn,
    intro: Item,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (NormalizedExit, Vec<HeaderImport>) {
    let mut projection = Projection {
        declaration_start: item_origin - intro.payload_view().spelling().unwrap().len(),
        visibility: Some(match item_word(&intro) {
            Some("pub") => Visibility::Public,
            Some("our") => Visibility::Our,
            _ => Visibility::Private,
        }),
        ..Projection::default()
    };
    let exit = use_declaration_projected_normalized(
        &mut projection,
        i,
        intro,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    );
    (
        exit,
        if projection.invalid {
            Vec::new()
        } else {
            projection.imports
        },
    )
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Terminal {
    Single,
    Group,
    Glob,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Separator {
    ColonColon,
    Slash,
}

type UseResult<T = Item> = Result<T, Item>;

pub(crate) fn use_declaration_selected_normalized(
    i: SyntaxIn,
    item: &Item,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    i.map(
        |lex: LexIn| {
            Some(use_declaration_selected_lexical(
                lex.remainder(),
                item,
                item_origin,
                fence,
            ))
        },
        |selected| selected,
    )
    .unwrap_or(false)
}

pub(crate) fn use_declaration_selected_lexical(
    source: &str,
    item: &Item,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    if item_word(item) == Some("use") {
        return true;
    }
    if !matches!(item_word(item), Some("my" | "our" | "pub")) {
        return false;
    }
    prefixed_use_candidate_normalized(source, item_origin, fence, item_word(item) == Some("my"))
}

fn prefixed_use_candidate_normalized(
    source: &str,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
    require_target: bool,
) -> bool {
    let TriviaObservation::Visible(first) =
        observe_fenced_trivia(source, item_origin, LineEntry::InLine, fence)
    else {
        return false;
    };
    if !first.present || first.indentation.is_some() {
        return false;
    }
    let Some((head, after_head)) = source_identifier(first.source) else {
        return false;
    };
    if head != "use" {
        return false;
    }
    if !require_target {
        return true;
    }
    let consumed = source.len() - after_head.len();
    let Some(after_head_origin) = item_origin.checked_add(consumed) else {
        return false;
    };
    let TriviaObservation::Visible(target) =
        observe_fenced_trivia(after_head, after_head_origin, LineEntry::InLine, fence)
    else {
        return false;
    };
    target.present && target.indentation.is_none() && use_tree_starter_source(target.source)
}

#[allow(clippy::too_many_arguments)]
fn use_declaration_projected_normalized(
    projection: &mut Projection,
    mut i: SyntaxIn,
    intro: Item,
    baseline: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::UseDeclaration.into());

    if item_word(&intro) == Some("use") {
        emit_item_as(&mut i, intro, SyntaxKind::UseKw);
    } else {
        emit_visibility(&mut i, intro);
        let mut keyword = next_use_item(i.rb(), &mut item_origin, &mut line_entry, fence);
        debug_assert!(inline_gap(&keyword));
        debug_assert_eq!(item_word(&keyword), Some("use"));
        keyword.emit_all_remaining_leading(&mut *i.state);
        emit_item_as(&mut i, keyword, SyntaxKind::UseKw);
    }

    let mut item = next_use_item(i.rb(), &mut item_origin, &mut line_entry, fence);
    if item.payload_view().is_boundary() {
        missing(
            i.rb(),
            &item,
            item_origin,
            import_role(ImportRole::Path),
            ExpectedSyntax::Path,
        );
        i.state.finish_node();
        return complete(handoff(item), line_entry);
    }
    let had_inline_gap = inline_gap(&item);
    if declaration_boundary(i.rb(), &item, stops, true) {
        missing(
            i.rb(),
            &item,
            item_origin,
            import_role(ImportRole::Path),
            ExpectedSyntax::Path,
        );
        i.state.finish_node();
        return complete(handoff(item), line_entry);
    }
    if had_inline_gap {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    if use_tree_starter(&item) && !had_inline_gap {
        missing(
            i.rb(),
            &item,
            item_origin,
            import_role(ImportRole::Path),
            ExpectedSyntax::Path,
        );
    }

    if !use_tree_starter(&item) {
        match recover_until(
            ImportRole::Path,
            i.rb(),
            item,
            |_, item, _, _, _| use_tree_retry(item),
            |_, _, _, _, _| false,
            baseline,
            stops,
            true,
            &mut item_origin,
            &mut line_entry,
            fence,
        ) {
            Ok((true, mut next)) => {
                next.emit_all_remaining_leading(&mut *i.state);
                item = next;
            }
            Ok((false, next)) | Err(next) => {
                i.state.finish_node();
                return complete(handoff(next), line_entry);
            }
        }
    }

    let item = match parse_use_tree(
        projection,
        i.rb(),
        item,
        baseline,
        stops,
        None,
        &mut item_origin,
        &mut line_entry,
        fence,
    ) {
        Ok(item) | Err(item) => item,
    };
    i.state.finish_node();
    complete(handoff(item), line_entry)
}

#[allow(clippy::too_many_arguments)]
fn parse_use_tree(
    projection: &mut Projection,
    mut i: SyntaxIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    outer_close: Option<char>,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult {
    debug_assert!(use_tree_starter(&item));
    projection.begin(*item_origin - item.payload_view().spelling().unwrap().len());
    i.state.start_node(SyntaxKind::UseTree.into());
    let result = (|| -> UseResult {
        let (terminal, item) = if exact_char(&item, '{') {
            (
                Terminal::Group,
                parse_group(
                    projection,
                    i.rb(),
                    item,
                    '}',
                    SyntaxKind::UseGroup,
                    baseline,
                    stops,
                    outer_close,
                    item_origin,
                    line_entry,
                    fence,
                )?,
            )
        } else if exact_char(&item, '(') {
            i.state.start_node(SyntaxKind::UsePath.into());
            let item =
                parse_operator_name(projection, i.rb(), item, item_origin, line_entry, fence);
            parse_path_tail(
                projection,
                i.rb(),
                item,
                baseline,
                stops,
                outer_close,
                item_origin,
                line_entry,
                fence,
            )?
        } else {
            let word = item_word(&item).expect("use-tree starter was a word");
            if word == "mod" {
                projection.form(HeaderImportForm::Mod);
                emit_item_as(&mut i, item, SyntaxKind::ModKw);
                let item = next_use_item(i.rb(), item_origin, line_entry, fence);
                parse_mod_target(
                    projection,
                    i.rb(),
                    item,
                    baseline,
                    stops,
                    outer_close,
                    item_origin,
                    line_entry,
                    fence,
                )?
            } else {
                let mut next = next_use_item(i.rb(), item_origin, line_entry, fence);
                match (word, separator(&next)) {
                    ("realm", Some(Separator::Slash)) => {
                        projection.form(HeaderImportForm::Realm);
                        emit_item_as(&mut i, item, SyntaxKind::RealmKw);
                        emit_separator(&mut i, next, Separator::Slash);
                        next = next_use_item(i.rb(), item_origin, line_entry, fence);
                        parse_marker_target(
                            projection,
                            i.rb(),
                            next,
                            baseline,
                            stops,
                            outer_close,
                            item_origin,
                            line_entry,
                            fence,
                        )?
                    }
                    ("band", Some(Separator::ColonColon)) => {
                        projection.form(HeaderImportForm::Band);
                        emit_item_as(&mut i, item, SyntaxKind::BandKw);
                        emit_separator(&mut i, next, Separator::ColonColon);
                        next = next_use_item(i.rb(), item_origin, line_entry, fence);
                        parse_marker_target(
                            projection,
                            i.rb(),
                            next,
                            baseline,
                            stops,
                            outer_close,
                            item_origin,
                            line_entry,
                            fence,
                        )?
                    }
                    _ => {
                        i.state.start_node(SyntaxKind::UsePath.into());
                        projection.segment(word);
                        emit_item_as(&mut i, item, SyntaxKind::Identifier);
                        parse_path_tail(
                            projection,
                            i.rb(),
                            next,
                            baseline,
                            stops,
                            outer_close,
                            item_origin,
                            line_entry,
                            fence,
                        )?
                    }
                }
            }
        };

        projection.frames.last_mut().unwrap().terminal = terminal;
        let item = if terminal != Terminal::Glob {
            parse_aliases(
                projection,
                i.rb(),
                item,
                baseline,
                stops,
                item_origin,
                line_entry,
                fence,
            )?
        } else {
            item
        };
        parse_qualifiers(
            projection,
            i.rb(),
            item,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
        )
    })();
    let end = match &result {
        Ok(item) | Err(item) => item.extent(*item_origin).recovery_range().start,
    };
    projection.finish(end);
    i.state.finish_node();
    result
}

#[allow(clippy::too_many_arguments)]
fn parse_mod_target(
    projection: &mut Projection,
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    outer_close: Option<char>,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult<(Terminal, Item)> {
    i.state.start_node(SyntaxKind::UsePath.into());
    if declaration_boundary(i.rb(), &item, stops, true) {
        missing(
            i.rb(),
            &item,
            *item_origin,
            import_role(ImportRole::Path),
            ExpectedSyntax::Path,
        );
        i.state.finish_node();
        return Err(item);
    }
    if inline_gap(&item) {
        item.emit_all_remaining_leading(&mut *i.state);
    } else if word_starter(&item) {
        missing(
            i.rb(),
            &item,
            *item_origin,
            import_role(ImportRole::Path),
            ExpectedSyntax::Path,
        );
    }
    let (present, item) = required_word(
        projection,
        ImportRole::Path,
        i.rb(),
        item,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    )?;
    if !present {
        i.state.finish_node();
        return Ok((Terminal::Single, item));
    }
    parse_path_tail(
        projection,
        i,
        item,
        baseline,
        stops,
        outer_close,
        item_origin,
        line_entry,
        fence,
    )
}

#[allow(clippy::too_many_arguments)]
fn parse_marker_target(
    projection: &mut Projection,
    mut i: SyntaxIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    outer_close: Option<char>,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult<(Terminal, Item)> {
    if exact_char(&item, '{') {
        let item = parse_group(
            projection,
            i,
            item,
            '}',
            SyntaxKind::UseGroup,
            baseline,
            stops,
            outer_close,
            item_origin,
            line_entry,
            fence,
        )?;
        return Ok((Terminal::Group, item));
    }
    if exact_char(&item, '*') {
        let item = parse_glob(
            projection,
            i,
            item,
            baseline,
            stops,
            outer_close,
            item_origin,
            line_entry,
            fence,
        )?;
        return Ok((Terminal::Glob, item));
    }

    i.state.start_node(SyntaxKind::UsePath.into());
    let (present, item) = required_path_segment(
        projection,
        i.rb(),
        item,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    )?;
    if !present {
        i.state.finish_node();
        return Ok((Terminal::Single, item));
    }
    parse_path_tail(
        projection,
        i,
        item,
        baseline,
        stops,
        outer_close,
        item_origin,
        line_entry,
        fence,
    )
}

#[allow(clippy::too_many_arguments)]
fn parse_path_tail(
    projection: &mut Projection,
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    outer_close: Option<char>,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult<(Terminal, Item)> {
    loop {
        let Some(separator_kind) = separator(&item) else {
            i.state.finish_node();
            return Ok((Terminal::Single, item));
        };
        projection.separator(separator_kind);
        emit_separator(&mut i, item, separator_kind);
        item = next_use_item(i.rb(), item_origin, line_entry, fence);
        if exact_char(&item, '{') {
            i.state.finish_node();
            item = parse_group(
                projection,
                i,
                item,
                '}',
                SyntaxKind::UseGroup,
                baseline,
                stops,
                outer_close,
                item_origin,
                line_entry,
                fence,
            )?;
            return Ok((Terminal::Group, item));
        }
        if exact_char(&item, '*') {
            i.state.finish_node();
            item = parse_glob(
                projection,
                i,
                item,
                baseline,
                stops,
                outer_close,
                item_origin,
                line_entry,
                fence,
            )?;
            return Ok((Terminal::Glob, item));
        }

        let (present, next) = required_path_segment(
            projection,
            i.rb(),
            item,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
        )?;
        item = next;
        if !present {
            i.state.finish_node();
            return Ok((Terminal::Single, item));
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn required_path_segment(
    projection: &mut Projection,
    mut i: SyntaxIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult<(bool, Item)> {
    if path_segment_starter_normalized(i.rb(), &item, *item_origin, *line_entry, fence) {
        return Ok((
            true,
            parse_path_segment(projection, i, item, item_origin, line_entry, fence),
        ));
    }
    if path_local_boundary(&item) {
        missing(
            i.rb(),
            &item,
            *item_origin,
            import_role(ImportRole::Path),
            ExpectedSyntax::Path,
        );
        return Ok((false, item));
    }
    if declaration_boundary(i.rb(), &item, stops, true) {
        missing(
            i.rb(),
            &item,
            *item_origin,
            import_role(ImportRole::Path),
            ExpectedSyntax::Path,
        );
        return Err(item);
    }
    let (retry, mut item) = recover_until(
        ImportRole::Path,
        i.rb(),
        item,
        path_segment_retry,
        |_, item, _, _, _| path_local_boundary(item),
        baseline,
        stops,
        true,
        item_origin,
        line_entry,
        fence,
    )?;
    if retry {
        item.emit_all_remaining_leading(&mut *i.state);
        Ok((
            true,
            parse_path_segment(projection, i, item, item_origin, line_entry, fence),
        ))
    } else {
        Ok((false, item))
    }
}

#[allow(clippy::too_many_arguments)]
fn required_word(
    projection: &mut Projection,
    role: ImportRole,
    mut i: SyntaxIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult<(bool, Item)> {
    if word_starter(&item) {
        projection.segment(item.payload_view().spelling().unwrap());
        emit_item_as(&mut i, item, SyntaxKind::Identifier);
        return Ok((true, next_use_item(i, item_origin, line_entry, fence)));
    }
    if reserved_use_atom(&item) {
        missing(
            i.rb(),
            &item,
            *item_origin,
            import_role(role),
            ExpectedSyntax::Identifier,
        );
        return Ok((false, item));
    }
    if declaration_boundary(i.rb(), &item, stops, true) {
        missing(
            i.rb(),
            &item,
            *item_origin,
            import_role(role),
            ExpectedSyntax::Identifier,
        );
        return Err(item);
    }
    let (retry, item) = recover_until(
        role,
        i.rb(),
        item,
        |_, item, _, _, _| word_retry(item),
        |_, item, _, _, _| reserved_use_atom(item),
        baseline,
        stops,
        true,
        item_origin,
        line_entry,
        fence,
    )?;
    if retry {
        projection.segment(item.payload_view().spelling().unwrap());
        emit_item_as(&mut i, item, SyntaxKind::Identifier);
        Ok((true, next_use_item(i, item_origin, line_entry, fence)))
    } else {
        Ok((false, item))
    }
}

fn parse_path_segment(
    projection: &mut Projection,
    mut i: SyntaxIn,
    item: Item,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> Item {
    if exact_char(&item, '(') {
        parse_operator_name(projection, i, item, item_origin, line_entry, fence)
    } else {
        projection.segment(item.payload_view().spelling().unwrap());
        emit_item_as(&mut i, item, SyntaxKind::Identifier);
        next_use_item(i, item_origin, line_entry, fence)
    }
}

fn parse_operator_name(
    projection: &mut Projection,
    mut i: SyntaxIn,
    open: Item,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> Item {
    i.state.start_node(SyntaxKind::OperatorName.into());
    emit_item_as(&mut i, open, SyntaxKind::LParen);
    let item = next_use_item(i.rb(), item_origin, line_entry, fence);
    if !item.leading_view().is_grammar_empty() || !operator_spelling(&item) {
        missing(
            i.rb(),
            &item,
            *item_origin,
            import_role(ImportRole::Path),
            ExpectedSyntax::OperatorName,
        );
        i.state.finish_node();
        return item;
    }
    projection.segment(item.payload_view().spelling().unwrap());
    emit_item_as(&mut i, item, SyntaxKind::Operator);
    let item = next_use_item(i.rb(), item_origin, line_entry, fence);
    if item.leading_view().is_grammar_empty() && exact_char(&item, ')') {
        emit_item_as(&mut i, item, SyntaxKind::RParen);
        let item = next_use_item(i.rb(), item_origin, line_entry, fence);
        i.state.finish_node();
        item
    } else {
        missing_close(
            i.rb(),
            &item,
            *item_origin,
            ')',
            ConstructRole::OperatorName,
        );
        i.state.finish_node();
        item
    }
}

#[allow(clippy::too_many_arguments)]
fn parse_group(
    projection: &mut Projection,
    mut i: SyntaxIn,
    open: Item,
    close: char,
    kind: SyntaxKind,
    baseline: usize,
    stops: Stops,
    outer_close: Option<char>,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult {
    projection.frames.last_mut().unwrap().terminal = Terminal::Group;
    i.state.start_node(kind.into());
    emit_item_as(&mut i, open, open_kind(close));
    let mut item = next_use_item(i.rb(), item_origin, line_entry, fence);
    let mut after_child = false;
    loop {
        if group_caller_boundary(i.rb(), &item, close, baseline, stops) {
            missing_close(
                i.rb(),
                &item,
                *item_origin,
                close,
                ConstructRole::ImportGroup,
            );
            i.state.finish_node();
            return Err(item);
        }
        let newline = item.leading_view().contains_line_break();
        item.emit_all_remaining_leading(&mut *i.state);
        if exact_char(&item, close) {
            emit_item_as(&mut i, item, close_kind(close));
            let item = next_use_item(i.rb(), item_origin, line_entry, fence);
            i.state.finish_node();
            return Ok(item);
        }
        if exact_char(&item, ',') {
            if !after_child {
                missing(
                    i.rb(),
                    &item,
                    *item_origin,
                    import_role(ImportRole::GroupEntry),
                    ExpectedSyntax::Path,
                );
            }
            emit_item_as(&mut i, item, SyntaxKind::Comma);
            item = next_use_item(i.rb(), item_origin, line_entry, fence);
            after_child = false;
            continue;
        }
        if mismatched_close(&item, close) {
            if outer_close.is_some_and(|outer| exact_char(&item, outer)) {
                missing_close(
                    i.rb(),
                    &item,
                    *item_origin,
                    close,
                    ConstructRole::ImportGroup,
                );
                i.state.finish_node();
                return Ok(item);
            }
            error_item(
                i.rb(),
                item,
                *item_origin,
                closing_role(close, ConstructRole::ImportGroup),
                ExpectedSyntax::Punctuation(PunctuationEvidence::Close(delimiter(close))),
            );
            item = next_use_item(i.rb(), item_origin, line_entry, fence);
            continue;
        }
        if use_tree_starter(&item) {
            if after_child && !newline {
                missing(
                    i.rb(),
                    &item,
                    *item_origin,
                    import_role(ImportRole::GroupEntry),
                    ExpectedSyntax::Punctuation(PunctuationEvidence::Comma),
                );
            }
            item = match parse_use_tree(
                projection,
                i.rb(),
                item,
                baseline,
                stops,
                Some(close),
                item_origin,
                line_entry,
                fence,
            ) {
                Ok(item) => item,
                Err(item) => {
                    i.state.finish_node();
                    return Err(item);
                }
            };
            after_child = true;
            continue;
        }

        item = match recover_group(
            i.rb(),
            item,
            close,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
        ) {
            Ok(item) => item,
            Err(item) => {
                i.state.finish_node();
                return Err(item);
            }
        };
        if exact_char(&item, ',') {
            emit_item_as(&mut i, item, SyntaxKind::Comma);
            item = next_use_item(i.rb(), item_origin, line_entry, fence);
            after_child = false;
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn parse_glob(
    projection: &mut Projection,
    mut i: SyntaxIn,
    star: Item,
    baseline: usize,
    stops: Stops,
    outer_close: Option<char>,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult {
    projection.invalid = true;
    i.state.start_node(SyntaxKind::UseGlob.into());
    emit_item_as(&mut i, star, SyntaxKind::Star);
    let item = next_use_item(i.rb(), item_origin, line_entry, fence);
    let result = (|| -> UseResult {
        let mut item = parse_aliases(
            projection,
            i.rb(),
            item,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
        )?;
        if inline_keyword(&item, "without") {
            item.emit_all_remaining_leading(&mut *i.state);
            emit_item_as(&mut i, item, SyntaxKind::WithoutKw);
            item = next_use_item(i.rb(), item_origin, line_entry, fence);
            if declaration_boundary(i.rb(), &item, stops, true) {
                missing(
                    i.rb(),
                    &item,
                    *item_origin,
                    import_role(ImportRole::Path),
                    ExpectedSyntax::Path,
                );
                return Err(item);
            }
            if inline_gap(&item) {
                item.emit_all_remaining_leading(&mut *i.state);
            } else if exclusion_starter(&item) {
                missing(
                    i.rb(),
                    &item,
                    *item_origin,
                    import_role(ImportRole::Path),
                    ExpectedSyntax::Path,
                );
            }
            let (present, next) = required_exclusion(
                projection,
                i.rb(),
                item,
                baseline,
                stops,
                outer_close,
                item_origin,
                line_entry,
                fence,
            )?;
            item = next;
            if present {
                while item.leading_view().is_grammar_empty() && exact_char(&item, ',') {
                    emit_item_as(&mut i, item, SyntaxKind::Comma);
                    item = next_use_item(i.rb(), item_origin, line_entry, fence);
                    if declaration_boundary(i.rb(), &item, stops, true) {
                        missing(
                            i.rb(),
                            &item,
                            *item_origin,
                            import_role(ImportRole::Path),
                            ExpectedSyntax::Path,
                        );
                        return Err(item);
                    }
                    item.emit_all_remaining_leading(&mut *i.state);
                    let (present, next) = required_exclusion(
                        projection,
                        i.rb(),
                        item,
                        baseline,
                        stops,
                        outer_close,
                        item_origin,
                        line_entry,
                        fence,
                    )?;
                    item = next;
                    if !present {
                        break;
                    }
                }
            }
        }
        Ok(item)
    })();
    i.state.finish_node();
    result
}

#[allow(clippy::too_many_arguments)]
fn required_exclusion(
    projection: &mut Projection,
    mut i: SyntaxIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    outer_close: Option<char>,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult<(bool, Item)> {
    if exclusion_starter(&item) {
        return Ok((
            true,
            parse_exclusion(
                projection,
                i,
                item,
                baseline,
                stops,
                outer_close,
                item_origin,
                line_entry,
                fence,
            )?,
        ));
    }
    if reserved_use_atom(&item) {
        missing(
            i.rb(),
            &item,
            *item_origin,
            import_role(ImportRole::Path),
            ExpectedSyntax::Path,
        );
        return Ok((false, item));
    }
    if declaration_boundary(i.rb(), &item, stops, true) {
        missing(
            i.rb(),
            &item,
            *item_origin,
            import_role(ImportRole::Path),
            ExpectedSyntax::Path,
        );
        return Err(item);
    }
    let (retry, item) = recover_until(
        ImportRole::Path,
        i.rb(),
        item,
        |_, item, _, _, _| {
            raw_char(item, '(') || raw_char(item, '{') || raw_char(item, '*') || word_retry(item)
        },
        |_, _, _, _, _| false,
        baseline,
        stops,
        true,
        item_origin,
        line_entry,
        fence,
    )?;
    if retry {
        Ok((
            true,
            parse_exclusion(
                projection,
                i,
                item,
                baseline,
                stops,
                outer_close,
                item_origin,
                line_entry,
                fence,
            )?,
        ))
    } else {
        Ok((false, item))
    }
}

#[allow(clippy::too_many_arguments)]
fn parse_exclusion(
    projection: &mut Projection,
    mut i: SyntaxIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    outer_close: Option<char>,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult {
    i.state.start_node(SyntaxKind::UseExclusion.into());
    let result = if exact_char(&item, '(') {
        if operator_name_follows(i.rb(), *item_origin, *line_entry, fence) {
            Ok(parse_operator_name(
                projection,
                i.rb(),
                item,
                item_origin,
                line_entry,
                fence,
            ))
        } else {
            parse_group(
                projection,
                i.rb(),
                item,
                ')',
                SyntaxKind::UseExclusionGroup,
                baseline,
                stops,
                outer_close,
                item_origin,
                line_entry,
                fence,
            )
        }
    } else if exact_char(&item, '{') {
        parse_group(
            projection,
            i.rb(),
            item,
            '}',
            SyntaxKind::UseExclusionGroup,
            baseline,
            stops,
            outer_close,
            item_origin,
            line_entry,
            fence,
        )
    } else if exact_char(&item, '*') {
        emit_item_as(&mut i, item, SyntaxKind::Star);
        Ok(next_use_item(i.rb(), item_origin, line_entry, fence))
    } else {
        emit_item_as(&mut i, item, SyntaxKind::Identifier);
        Ok(next_use_item(i.rb(), item_origin, line_entry, fence))
    };
    i.state.finish_node();
    result
}

#[allow(clippy::too_many_arguments)]
fn parse_aliases(
    projection: &mut Projection,
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult {
    while inline_keyword(&item, "as") {
        item.emit_all_remaining_leading(&mut *i.state);
        i.state.start_node(SyntaxKind::UseAlias.into());
        emit_item_as(&mut i, item, SyntaxKind::AsKw);
        item = next_use_item(i.rb(), item_origin, line_entry, fence);
        if declaration_boundary(i.rb(), &item, stops, true) {
            projection.invalid = true;
            missing(
                i.rb(),
                &item,
                *item_origin,
                import_role(ImportRole::Alias),
                ExpectedSyntax::Identifier,
            );
            i.state.finish_node();
            return Err(item);
        }
        if inline_gap(&item) {
            item.emit_all_remaining_leading(&mut *i.state);
        } else if word_starter(&item) {
            missing(
                i.rb(),
                &item,
                *item_origin,
                import_role(ImportRole::Alias),
                ExpectedSyntax::Identifier,
            );
        }
        projection.alias = true;
        let result = required_word(
            projection,
            ImportRole::Alias,
            i.rb(),
            item,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
        );
        projection.alias = false;
        i.state.finish_node();
        if result.is_err() {
            projection.invalid = true;
        }
        let (present, next) = result?;
        if !present {
            projection.invalid = true;
        }
        item = next;
    }
    Ok(item)
}

#[allow(clippy::too_many_arguments)]
fn parse_qualifiers(
    projection: &mut Projection,
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult {
    let version = inline_version(&item);
    let anchor = !version && inline_keyword(&item, "with");
    if !version && !anchor {
        return Ok(item);
    }

    projection.invalid = true;
    i.state.start_node(SyntaxKind::UseQualifiers.into());
    let result = (|| -> UseResult {
        if version {
            item.emit_all_remaining_leading(&mut *i.state);
            i.state.start_node(SyntaxKind::UseVersion.into());
            emit_item_as(&mut i, item, SyntaxKind::Version);
            i.state.finish_node();
            item = next_use_item(i.rb(), item_origin, line_entry, fence);
            if inline_keyword(&item, "with") {
                item = parse_anchor(
                    projection,
                    i.rb(),
                    item,
                    baseline,
                    stops,
                    item_origin,
                    line_entry,
                    fence,
                )?;
            }
        } else {
            item = parse_anchor(
                projection,
                i.rb(),
                item,
                baseline,
                stops,
                item_origin,
                line_entry,
                fence,
            )?;
        }
        Ok(item)
    })();
    i.state.finish_node();
    result
}

#[allow(clippy::too_many_arguments)]
fn parse_anchor(
    projection: &mut Projection,
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult {
    item.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::UseAnchor.into());
    emit_item_as(&mut i, item, SyntaxKind::WithKw);
    item = next_use_item(i.rb(), item_origin, line_entry, fence);
    i.state.start_node(SyntaxKind::UsePath.into());
    if declaration_boundary(i.rb(), &item, stops, true) {
        missing(
            i.rb(),
            &item,
            *item_origin,
            import_role(ImportRole::Path),
            ExpectedSyntax::Path,
        );
        i.state.finish_node();
        i.state.finish_node();
        return Err(item);
    }
    if inline_gap(&item) {
        item.emit_all_remaining_leading(&mut *i.state);
    } else if word_starter(&item) {
        missing(
            i.rb(),
            &item,
            *item_origin,
            import_role(ImportRole::Path),
            ExpectedSyntax::Path,
        );
    }
    let result = (|| -> UseResult {
        let (present, mut item) = required_word(
            projection,
            ImportRole::Path,
            i.rb(),
            item,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
        )?;
        if present {
            while let Some(separator_kind) = separator(&item) {
                emit_separator(&mut i, item, separator_kind);
                item = next_use_item(i.rb(), item_origin, line_entry, fence);
                let (present, next) = required_word(
                    projection,
                    ImportRole::Path,
                    i.rb(),
                    item,
                    baseline,
                    stops,
                    item_origin,
                    line_entry,
                    fence,
                )?;
                item = next;
                if !present {
                    break;
                }
            }
        }
        Ok(item)
    })();
    i.state.finish_node();
    i.state.finish_node();
    result
}

#[allow(clippy::too_many_arguments)]
fn recover_until<C, L>(
    role: ImportRole,
    mut i: SyntaxIn,
    mut item: Item,
    candidate: C,
    local_boundary: L,
    _baseline: usize,
    stops: Stops,
    newline_boundary: bool,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> Result<(bool, Item), Item>
where
    C: Fn(LexIn, &Item, usize, LineEntry, Option<&FenceBoundary>) -> bool,
    L: Fn(LexIn, &Item, usize, LineEntry, Option<&FenceBoundary>) -> bool,
{
    if declaration_boundary(i.rb(), &item, stops, newline_boundary) {
        return Err(item);
    }
    if i.rb()
        .map(
            |lex: LexIn| Some(local_boundary(lex, &item, *item_origin, *line_entry, fence)),
            |x| x,
        )
        .unwrap()
    {
        return Ok((false, item));
    }
    item.emit_all_remaining_leading(&mut *i.state);
    let result = emit_recovery_error_run(
        i.rb(),
        |run| {
            let start = item.extent(*item_origin).recovery_range().start;
            loop {
                let kind = SyntaxKind::Unknown;
                let extent = run.emit_item_as(item, *item_origin, kind);
                item = run.lexical(|lex| next_use_item_lex(lex, item_origin, line_entry, fence));
                let (boundary, accepted, local) = run.lexical(|mut lex| {
                    (
                        declaration_boundary_lex(lex.rb(), &item, stops, newline_boundary),
                        candidate(lex.rb(), &item, *item_origin, *line_entry, fence),
                        local_boundary(lex, &item, *item_origin, *line_entry, fence),
                    )
                });
                if boundary || accepted || local {
                    run.append_unexpected(UnexpectedSyntax::Token {
                        range: start..extent.recovery_range().end,
                        category: UnexpectedCategory::OtherCharacter,
                    });
                    return if boundary {
                        Err(item)
                    } else {
                        Ok((accepted, item))
                    };
                }
            }
        },
        |range, unexpected| {
            recovery_draft(
                import_role(role),
                if role == ImportRole::Alias {
                    ExpectedSyntax::Identifier
                } else {
                    ExpectedSyntax::Path
                },
                RecoveryKind::Error,
                range,
                unexpected,
            )
        },
    );
    result
}

#[allow(clippy::too_many_arguments)]
fn recover_group(
    i: SyntaxIn,
    mut item: Item,
    close: char,
    baseline: usize,
    stops: Stops,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult {
    item.emit_all_remaining_leading(&mut *i.state);
    emit_recovery_error_run(
        i,
        |run| {
            let start = item.extent(*item_origin).recovery_range().start;
            loop {
                let kind = SyntaxKind::Unknown;
                let extent = run.emit_item_as(item, *item_origin, kind);
                item = run.lexical(|lex| next_use_item_lex(lex, item_origin, line_entry, fence));
                let boundary = run
                    .lexical(|lex| group_caller_boundary_lex(lex, &item, close, baseline, stops));
                if boundary
                    || use_tree_retry(&item)
                    || raw_char(&item, ',')
                    || raw_char(&item, close)
                {
                    run.append_unexpected(UnexpectedSyntax::Token {
                        range: start..extent.recovery_range().end,
                        category: UnexpectedCategory::OtherCharacter,
                    });
                    return if boundary { Err(item) } else { Ok(item) };
                }
            }
        },
        |range, unexpected| {
            recovery_draft(
                import_role(ImportRole::GroupEntry),
                ExpectedSyntax::Path,
                RecoveryKind::Error,
                range,
                unexpected,
            )
        },
    )
}

fn import_role(role: ImportRole) -> GrammarRole {
    GrammarRole::Declaration(DeclarationRole::Import(role))
}

fn delimiter(close: char) -> Delimiter {
    if close == ')' {
        Delimiter::Parenthesis
    } else {
        Delimiter::Brace
    }
}

fn closing_role(close: char, owner: ConstructRole) -> GrammarRole {
    GrammarRole::ClosingDelimiter {
        owner,
        delimiter: delimiter(close),
    }
}

fn recovery_draft(
    role: GrammarRole,
    expected: ExpectedSyntax,
    kind: RecoveryKind,
    range: Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    RecoveryDraft::new(
        RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        Arc::from([SyntaxExpectation {
            role,
            expected,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        0,
    )
}

fn missing(i: SyntaxIn, item: &Item, origin: usize, role: GrammarRole, expected: ExpectedSyntax) {
    let at = item.payload_view().pending_boundary().map_or_else(
        || item.extent(origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    );
    emit_recovery_missing(i, LeadingTrivia::default(), at, |range| {
        recovery_draft(role, expected, RecoveryKind::Missing, range, Arc::from([]))
    });
}

fn missing_close(i: SyntaxIn, item: &Item, origin: usize, close: char, owner: ConstructRole) {
    missing(
        i,
        item,
        origin,
        closing_role(close, owner),
        ExpectedSyntax::Punctuation(PunctuationEvidence::Close(delimiter(close))),
    );
}

fn error_item(
    i: SyntaxIn,
    mut item: Item,
    origin: usize,
    role: GrammarRole,
    expected: ExpectedSyntax,
) {
    item.emit_all_remaining_leading(&mut *i.state);
    emit_recovery_error_run(
        i,
        |run| {
            let kind = SyntaxKind::Unknown;
            let extent = run.emit_item_as(item, origin, kind);
            run.append_unexpected(UnexpectedSyntax::Token {
                range: extent.recovery_range(),
                category: UnexpectedCategory::OtherCharacter,
            });
        },
        |range, unexpected| recovery_draft(role, expected, RecoveryKind::Error, range, unexpected),
    );
}

fn declaration_boundary(i: SyntaxIn, item: &Item, stops: Stops, newline: bool) -> bool {
    i.map(
        |lex: LexIn| Some(declaration_boundary_lex(lex, item, stops, newline)),
        |x| x,
    )
    .unwrap()
}

fn declaration_boundary_lex(mut i: LexIn, item: &Item, stops: Stops, newline: bool) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || newline && item.leading_view().contains_line_break()
        || crate::lexical::observation::is_active_stop_lex(i.rb(), item, stops)
        || matches!(
            token_kind(item),
            Some(
                TokenKind::Comma
                    | TokenKind::Semicolon
                    | TokenKind::LBracket
                    | TokenKind::RParen
                    | TokenKind::RBracket
                    | TokenKind::RBrace
            )
        )
}

fn group_caller_boundary(
    i: SyntaxIn,
    item: &Item,
    close: char,
    baseline: usize,
    stops: Stops,
) -> bool {
    i.map(
        |lex: LexIn| Some(group_caller_boundary_lex(lex, item, close, baseline, stops)),
        |x| x,
    )
    .unwrap()
}

fn group_caller_boundary_lex(
    mut i: LexIn,
    item: &Item,
    close: char,
    baseline: usize,
    stops: Stops,
) -> bool {
    if exact_char(item, ',') || exact_char(item, close) {
        return false;
    }
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || crate::lexical::observation::is_active_stop_lex(i.rb(), item, stops)
        || token_kind(item) == Some(TokenKind::Semicolon)
        || token_kind(item) == Some(TokenKind::LBracket)
        || indentation_after_newline(item.leading_view())
            .is_some_and(|indentation| indentation <= baseline)
            && is_exact_canonical_statement_intro(item)
}

fn is_exact_canonical_statement_intro(item: &Item) -> bool {
    matches!(
        item_word(item),
        Some("use" | "mod" | "struct" | "type" | "for" | "my" | "our" | "pub")
    )
}

pub(crate) fn next_use_item_lex(
    mut i: LexIn,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> Item {
    let before = i.remainder().len();
    let CurrentItem {
        item,
        next_line_entry,
    } = current_item(
        i.rb(),
        *item_origin,
        *line_entry,
        fence,
        |lex, _, _, _, _| scan_use_payload(lex),
    )
    .expect("Use scanning is total");
    *item_origin += before - i.remainder().len();
    *line_entry = next_line_entry;
    item
}

fn next_use_item(
    mut i: SyntaxIn,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> Item {
    i.token(|lex| Some(next_use_item_lex(lex, item_origin, line_entry, fence)))
        .unwrap()
}

fn scan_use_payload(mut i: LexIn) -> Option<AcceptedPayload> {
    let token = if let Some(version) = i.token(scan_version_token) {
        version
    } else if let Some(identifier) = i.token(scan_identifier) {
        identifier
    } else if let Some(arrow) = i.token(scan_arm_arrow) {
        arrow
    } else if let Some(separator) =
        i.token(|lex| scan_pair_token(lex, ':', ':', TokenKind::PathSeparator))
    {
        separator
    } else if let Some(punctuation) = i.token(scan_punctuation) {
        punctuation
    } else if let Some(slash) = i.token(|lex| scan_character_token(lex, '/', TokenKind::Operator)) {
        slash
    } else if let Some(operator) = i.token(scan_operator_token) {
        operator
    } else {
        i.token(scan_unknown)?
    };
    Some(AcceptedPayload {
        payload: CurrentPayload::Token(token),
        next_line_entry: LineEntry::InLine,
    })
}

fn scan_version_token(mut i: LexIn) -> Option<Token> {
    let (accepted, text) = i.rb().with_str(|mut version| {
        (version.next()? == 'v').then_some(())?;
        version
            .remainder()
            .chars()
            .next()
            .is_some_and(|character| character.is_ascii_digit())
            .then_some(())?;
        version.next()?;
        while version.remainder().chars().next().is_some_and(|character| {
            character.is_ascii_alphanumeric() || matches!(character, '.' | '-' | '+')
        }) {
            version.next()?;
        }
        Some(())
    });
    accepted?;
    Some(Token {
        kind: TokenKind::Identifier,
        text: text.into(),
    })
}

fn scan_pair_token(mut i: LexIn, first: char, second: char, kind: TokenKind) -> Option<Token> {
    let (accepted, text) = i.rb().with_str(|mut pair| {
        (pair.next()? == first).then_some(())?;
        (pair.next()? == second).then_some(())
    });
    accepted?;
    Some(Token {
        kind,
        text: text.into(),
    })
}

fn scan_character_token(mut i: LexIn, expected: char, kind: TokenKind) -> Option<Token> {
    let (accepted, text) = i
        .rb()
        .with_str(|mut one| (one.next()? == expected).then_some(()));
    accepted?;
    Some(Token {
        kind,
        text: text.into(),
    })
}

fn scan_operator_token(mut i: LexIn) -> Option<Token> {
    let (accepted, text) = i.rb().with_str(|mut spelling| {
        is_use_operator_character(spelling.next()?).then_some(())?;
        while spelling
            .remainder()
            .chars()
            .next()
            .is_some_and(is_use_operator_character)
        {
            spelling.next()?;
        }
        Some(())
    });
    accepted?;
    Some(Token {
        kind: TokenKind::Operator,
        text: text.into(),
    })
}

fn emit_item_as(i: &mut SyntaxIn, item: Item, kind: SyntaxKind) {
    item.emit_remaining(&mut *i.state, kind);
}

fn emit_separator(i: &mut SyntaxIn, item: Item, separator: Separator) {
    let kind = match separator {
        Separator::ColonColon => SyntaxKind::ColonColon,
        Separator::Slash => SyntaxKind::Slash,
    };
    emit_item_as(i, item, kind);
}

fn emit_visibility(i: &mut SyntaxIn, item: Item) {
    let kind = match item.payload_view().spelling() {
        Some("my") => SyntaxKind::MyKw,
        Some("our") => SyntaxKind::OurKw,
        Some("pub") => SyntaxKind::PubKw,
        _ => unreachable!("use visibility was selected from exact words"),
    };
    emit_item_as(i, item, kind);
}

fn item_word(item: &Item) -> Option<&str> {
    (item.payload_view().token_kind() == Some(TokenKind::Identifier))
        .then(|| item.payload_view().spelling())
        .flatten()
}

fn exact_char(item: &Item, expected: char) -> bool {
    item.leading_view().is_grammar_empty()
        && item
            .payload_view()
            .spelling()
            .is_some_and(|text| text.len() == expected.len_utf8() && text.starts_with(expected))
}

fn inline_gap(item: &Item) -> bool {
    !item.leading_view().is_grammar_empty() && !item.leading_view().contains_line_break()
}

fn inline_keyword(item: &Item, expected: &str) -> bool {
    inline_gap(item) && item_word(item) == Some(expected)
}

fn inline_version(item: &Item) -> bool {
    inline_gap(item) && item_word(item).is_some_and(version_starter)
}

fn separator(item: &Item) -> Option<Separator> {
    if !item.leading_view().is_grammar_empty() {
        return None;
    }
    match item.payload_view().spelling() {
        Some("::") => Some(Separator::ColonColon),
        Some("/") => Some(Separator::Slash),
        _ => None,
    }
}

fn use_tree_starter(item: &Item) -> bool {
    exact_char(item, '{')
        || exact_char(item, '(')
        || item_word(item).is_some_and(|word| word == "mod" || use_identifier_spelling(word))
}

fn use_tree_starter_source(source: &str) -> bool {
    matches!(source.chars().next(), Some('{' | '('))
        || source.starts_with("mod")
            && source_identifier(source).is_some_and(|(word, _)| word == "mod")
        || source_identifier(source).is_some_and(|(word, _)| use_identifier_spelling(word))
}

fn path_segment_starter_normalized(
    i: SyntaxIn,
    item: &Item,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> bool {
    word_starter(item)
        || exact_char(item, '(') && operator_name_follows(i, item_origin, line_entry, fence)
}

fn operator_name_follows(
    mut i: SyntaxIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> bool {
    let mut accepted = false;
    let _: Option<()> = i.token(|lex| {
        let CurrentItem { item, .. } =
            current_item(lex, item_origin, line_entry, fence, |lex, _, _, _, _| {
                scan_use_payload(lex)
            })?;
        accepted = operator_spelling(&item);
        None
    });
    accepted
}

fn exclusion_starter(item: &Item) -> bool {
    exact_char(item, '(') || exact_char(item, '{') || exact_char(item, '*') || word_starter(item)
}

fn word_starter(item: &Item) -> bool {
    item.leading_view().is_grammar_empty() && item_word(item).is_some_and(use_identifier_spelling)
}

fn reserved_use_atom(item: &Item) -> bool {
    item.leading_view().is_grammar_empty()
        && item_word(item).is_some_and(|word| !use_identifier_spelling(word))
}

fn path_local_boundary(item: &Item) -> bool {
    separator(item).is_some()
        || reserved_use_atom(item)
        || inline_keyword(item, "as")
        || inline_keyword(item, "with")
        || inline_version(item)
}

fn mismatched_close(item: &Item, close: char) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::RParen | TokenKind::RBrace)
    ) && !exact_char(item, close)
}

fn operator_spelling(item: &Item) -> bool {
    item.leading_view().is_grammar_empty()
        && item.payload_view().token_kind() == Some(TokenKind::Operator)
        && item
            .payload_view()
            .spelling()
            .is_some_and(|text| text.chars().all(is_use_operator_character))
}

fn version_starter(word: &str) -> bool {
    word.strip_prefix('v')
        .and_then(|suffix| suffix.chars().next())
        .is_some_and(|character| character.is_ascii_digit())
}

fn use_identifier_spelling(word: &str) -> bool {
    !matches!(word, "mod" | "as" | "with" | "without") && !version_starter(word)
}

fn close_kind(close: char) -> SyntaxKind {
    match close {
        ')' => SyntaxKind::RParen,
        '}' => SyntaxKind::RBrace,
        _ => unreachable!("use groups are parenthesized or braced"),
    }
}

fn open_kind(close: char) -> SyntaxKind {
    match close {
        ')' => SyntaxKind::LParen,
        '}' => SyntaxKind::LBrace,
        _ => unreachable!("use groups are parenthesized or braced"),
    }
}

fn is_use_operator_character(character: char) -> bool {
    !character.is_whitespace()
        && character != '_'
        && !is_xid_continue(character)
        && !matches!(
            character,
            '(' | ')' | '[' | ']' | '{' | '}' | ',' | ':' | '/' | ';'
        )
}

fn raw_char(item: &Item, expected: char) -> bool {
    item.payload_view()
        .spelling()
        .is_some_and(|text| text.len() == expected.len_utf8() && text.starts_with(expected))
}
fn word_retry(item: &Item) -> bool {
    item_word(item).is_some_and(use_identifier_spelling)
}
fn use_tree_retry(item: &Item) -> bool {
    raw_char(item, '{') || raw_char(item, '(') || item_word(item) == Some("mod") || word_retry(item)
}
fn path_segment_retry(
    mut i: LexIn,
    item: &Item,
    origin: usize,
    line: LineEntry,
    fence: Option<&FenceBoundary>,
) -> bool {
    if word_retry(item) {
        return true;
    }
    if !raw_char(item, '(') {
        return false;
    }
    let mut accepted = false;
    let _: Option<()> = i.token(|lex| {
        let CurrentItem { item, .. } =
            current_item(lex, origin, line, fence, |lex, _, _, _, _| {
                scan_use_payload(lex)
            })?;
        accepted = operator_spelling(&item);
        None
    });
    accepted
}
