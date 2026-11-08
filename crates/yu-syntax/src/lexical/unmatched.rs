//! WP-18 source matching, independent of grammar admission and recovery.
use super::opaque_region::skip_source_opaque;
use crate::{
    cursor::{LexIn, LexRecover},
    operator_table::OperatorTable,
};
use chasa_recover::In;

pub(crate) struct UnmatchedOpeners {
    unmatched: Vec<bool>,
    paired_closers: Vec<bool>,
    lines: Vec<(usize, usize)>,
}

impl UnmatchedOpeners {
    pub(crate) fn scan(source: &str, operators: &OperatorTable) -> Self {
        let mut unmatched = vec![false; source.len()];
        let mut paired_closers = vec![false; source.len()];
        // Each frame also links to the previous opener of its own kind. A
        // foreign closer with no opener is O(1), even on `((((...]]]]...`.
        let mut stack: Vec<(usize, usize, Option<usize>)> = Vec::new();
        let mut last = [None; 3];
        let mut remaining = source;
        let mut recover = LexRecover::new(operators);
        let mut first_on_line = true;
        let mut indentation = 0;
        let mut lines = vec![(0, 0)];
        while !remaining.is_empty() {
            let origin = source.len() - remaining.len();
            let before = remaining;
            let skipped = {
                let i: LexIn = In::new(&mut remaining, &mut recover, ());
                skip_source_opaque(
                    i,
                    origin,
                    first_on_line.then_some(indentation),
                    &mut unmatched,
                )
            };
            if !skipped {
                let ch = remaining.chars().next().unwrap();
                remaining = if ch == '-' {
                    &remaining[remaining.bytes().take_while(|byte| *byte == b'-').count()..]
                } else {
                    super::lexer::source_identifier(remaining)
                        .map_or(&remaining[ch.len_utf8()..], |(_, suffix)| suffix)
                };
                let kind = match ch {
                    '(' | ')' => Some(0),
                    '[' | ']' => Some(1),
                    '{' | '}' => Some(2),
                    _ => None,
                };
                if let Some(kind) = kind {
                    if matches!(ch, '(' | '[' | '{') {
                        let previous = last[kind];
                        last[kind] = Some(stack.len());
                        stack.push((origin, kind, previous));
                    } else if let Some(index) = last[kind] {
                        paired_closers[origin] = true;
                        while stack.len() > index {
                            let (at, popped_kind, previous) = stack.pop().unwrap();
                            last[popped_kind] = previous;
                            if stack.len() != index {
                                unmatched[at] = true;
                            }
                        }
                    }
                }
            }
            // Each settled byte is charged once here, including opaque bodies;
            // never search backward for the start of a physical line.
            for (offset, ch) in before[..before.len() - remaining.len()].char_indices() {
                match ch {
                    '\r' | '\n' => {
                        first_on_line = true;
                        indentation = 0;
                        lines.push((origin + offset + 1, 0));
                    }
                    ' ' | '\t' if first_on_line => {
                        indentation += 1;
                        lines.last_mut().unwrap().1 = indentation;
                    }
                    _ => first_on_line = false,
                }
            }
        }
        for (at, _, _) in stack {
            unmatched[at] = true;
        }
        Self {
            unmatched,
            paired_closers,
            lines,
        }
    }

    pub(crate) fn line_indentation(&self, position: usize) -> usize {
        let line = self.lines.partition_point(|(start, _)| *start <= position);
        self.lines[line - 1].1
    }

    pub(crate) fn contains(&self, position: usize) -> bool {
        self.unmatched.get(position).copied().unwrap_or(false)
    }

    pub(crate) fn closer_is_paired(&self, position: usize) -> bool {
        self.paired_closers.get(position).copied().unwrap_or(false)
    }
}
