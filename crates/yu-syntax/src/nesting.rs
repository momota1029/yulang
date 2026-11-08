//! One stack budget across grammar families, header discovery and embedded Yulang.
use std::cell::Cell;

use crate::{
    SyntaxKind,
    cursor::SyntaxIn,
    handoff::{NormalizedExit, complete, handoff},
    lexical::{
        current_item::{LineEntry, current_item},
        item::Item,
        lexer::scan_statement_payload,
        yumark::FenceBoundary,
    },
};

// Support 512 KiB threads as well as the usual 2 MiB test threads. Reserve
// 256 KiB for the caller, the next unchecked grammar segment and recovery.
// This is a byte budget, not a construct count: mixed nesting and direct lambda
// operands must spend the same budget. See notes/audit/ls-recovery-audit.md.
pub(crate) const STACK_BUDGET: usize = 256 * 1024;
// On targets without a native stack-address model, bound *all* active grammar
// entries together. Eight segments plus four segments of recovery reserve
// fit 512 KiB with the measured debug guard gaps (see the audit).
const FALLBACK_DEPTH: usize = 8;
// Heap-driven Yumark frames need no native stack per level. Keep their existing
// 10,000-level contract while bounding recovery/diagnostic output for hostile
// documents (in particular an unclosed frame at every level).
pub(crate) const ITERATIVE_LIMIT: usize = 16_384;

#[derive(Clone, Copy, Default)]
struct State {
    base: usize,
    depth: usize,
    #[cfg(test)]
    address: usize,
}
thread_local! {
    static STATE: Cell<State> = const { Cell::new(State { base: 0, depth: 0, #[cfg(test)] address: 0 }) };
}

pub(crate) struct Guard {
    previous: State,
    exhausted: bool,
}

impl Guard {
    // Taking an address never dereferences an expired frame. abs_diff handles
    // either stack direction; unknown/virtual-stack targets use the counter.
    #[inline(never)]
    pub(crate) fn enter() -> Self {
        let marker = 0u8;
        let address = std::ptr::addr_of!(marker).addr();
        STATE.with(|state| {
            let previous = state.get();
            let base = if previous.depth == 0 {
                address
            } else {
                previous.base
            };
            let depth = previous.depth + 1;
            let native_stack = cfg!(any(
                target_arch = "x86",
                target_arch = "x86_64",
                target_arch = "arm",
                target_arch = "aarch64",
                target_arch = "riscv32",
                target_arch = "riscv64",
                target_arch = "powerpc",
                target_arch = "powerpc64",
                target_arch = "s390x"
            ));
            let exhausted = exceeds_budget(base, address, depth, native_stack);
            #[cfg(test)]
            METRICS.with(|metrics| {
                let (step, used) = metrics.get();
                metrics.set((
                    step.max(if previous.depth == 0 {
                        0
                    } else {
                        previous.address.abs_diff(address)
                    }),
                    used.max(base.abs_diff(address)),
                ));
            });
            state.set(State {
                base,
                depth,
                #[cfg(test)]
                address,
            });
            Self {
                previous,
                exhausted,
            }
        })
    }

    pub(crate) fn exhausted(&self) -> bool {
        self.exhausted
    }
}

impl Drop for Guard {
    fn drop(&mut self) {
        STATE.with(|state| state.set(self.previous));
    }
}

impl SyntaxIn<'_, '_, '_> {
    /// Retain an accepted primary and its remaining region without calling any
    /// grammar. A matched primary ends at its own close; an unclosed region
    /// stops before a same/outer-indented line, allowing later statements to run.
    pub(crate) fn recover_nesting(
        &mut self,
        item: Item,
        origin: usize,
        line: LineEntry,
        fence: Option<&FenceBoundary>,
    ) -> NormalizedExit {
        let length = self.skip_nesting(item);
        let baseline = self.nesting_indentation();
        let before = self.remainder().len();
        let mut current = self
            .token(|lex| {
                current_item(
                    lex,
                    origin + length,
                    line,
                    fence,
                    |lex, leading, origin, fence, _| {
                        scan_statement_payload(lex, leading, origin, fence, baseline, 0)
                    },
                )
            })
            .expect("recovery successor scanning is total");
        let successor = origin + length + before - self.remainder().len();
        self.mark_nesting_boundary(&mut current.item, successor);
        complete(handoff(current.item), current.next_line_entry)
    }

    pub(crate) fn skip_nesting(&mut self, item: Item) -> usize {
        let spelling = item.payload_view().spelling().unwrap_or("");
        let initial_close = match spelling {
            "(" => Some(')'),
            "[" => Some(']'),
            "{" => Some('}'),
            _ => None,
        };
        let source = self.remainder();
        let baseline = self.nesting_indentation();
        let length = if spelling.starts_with('"') || matches!(spelling, "~\"" | "'[" | "'{") {
            let mut remaining = source;
            let mut recover = crate::cursor::LexRecover::new(self.operators());
            let lex = chasa_recover::In::new(&mut remaining, &mut recover, ());
            crate::lexical::opaque_region::finish_opaque_opener(lex, spelling, 0, None).length
        } else {
            opaque_length(source, initial_close, baseline)
        };
        self.state.start_node(SyntaxKind::NestingTooDeep.into());
        item.emit_remaining_error(self.state);
        if length > 0 {
            self.state
                .token(SyntaxKind::Error.into(), &source[..length]);
        }
        self.advance_bytes(length);
        self.state.finish_node();
        length
    }
}

fn opaque_length(source: &str, initial_close: Option<char>, baseline: usize) -> usize {
    let mut closes: Vec<char> = initial_close.into_iter().collect();
    let mut chars = source.char_indices().peekable();
    while let Some((at, ch)) = chars.next() {
        if matches!(ch, '\r' | '\n') {
            let rest = &source[at + ch.len_utf8()..];
            let indent = rest
                .bytes()
                .take_while(|b| matches!(b, b' ' | b'\t'))
                .count();
            let text = &rest[indent..];
            if !text.starts_with(['\r', '\n']) && indent <= baseline {
                return at;
            }
        }
        match ch {
            '(' => closes.push(')'),
            '[' => closes.push(']'),
            '{' => closes.push('}'),
            ')' | ']' | '}' => {
                if closes.is_empty() {
                    return at;
                }
                if closes.last() == Some(&ch) {
                    closes.pop();
                    if closes.is_empty() && initial_close.is_some() {
                        return at + ch.len_utf8();
                    }
                }
            }
            '"' => {
                while let Some((_, next)) = chars.next() {
                    if next == '\\' {
                        chars.next();
                    } else if next == '"' {
                        break;
                    }
                }
            }
            '/' if chars.peek().is_some_and(|(_, c)| *c == '/') => {
                while chars.peek().is_some_and(|(_, c)| !matches!(c, '\r' | '\n')) {
                    chars.next();
                }
            }
            '/' if chars.peek().is_some_and(|(_, c)| *c == '*') => {
                chars.next();
                let mut depth = 1usize;
                while let Some((_, c)) = chars.next() {
                    if c == '/' && chars.peek().is_some_and(|(_, c)| *c == '*') {
                        chars.next();
                        depth += 1;
                    } else if c == '*' && chars.peek().is_some_and(|(_, c)| *c == '/') {
                        chars.next();
                        depth -= 1;
                        if depth == 0 {
                            break;
                        }
                    }
                }
            }
            _ => {}
        }
    }
    source.len()
}

#[cfg(test)]
thread_local! {
    static METRICS: Cell<(usize, usize)> = const { Cell::new((0, 0)) };
}
#[cfg(test)]
pub(crate) fn take_metrics() -> (usize, usize) {
    METRICS.with(|metrics| metrics.replace((0, 0)))
}

/// Closing punctuation cannot descend and remains owned by the enclosing rule.
pub(crate) fn may_descend(item: &Item) -> bool {
    use crate::lexical::item::TokenKind;
    !item.payload_view().is_boundary()
        && !item.payload_view().is_eof()
        && !matches!(
            item.payload_view().token_kind(),
            Some(
                TokenKind::RParen
                    | TokenKind::RBracket
                    | TokenKind::RBrace
                    | TokenKind::Comma
                    | TokenKind::Semicolon
            )
        )
}

fn exceeds_budget(base: usize, address: usize, depth: usize, native_stack: bool) -> bool {
    if native_stack {
        base.abs_diff(address) > STACK_BUDGET
    } else {
        depth > FALLBACK_DEPTH
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn both_stack_directions_and_the_address_free_fallback_are_bounded() {
        let base = 2 * STACK_BUDGET;
        for address in [base - STACK_BUDGET, base + STACK_BUDGET] {
            assert!(!exceeds_budget(base, address, usize::MAX, true));
        }
        for address in [base - STACK_BUDGET - 1, base + STACK_BUDGET + 1] {
            assert!(exceeds_budget(base, address, 0, true));
        }
        assert!(!exceeds_budget(0, usize::MAX, FALLBACK_DEPTH, false));
        assert!(exceeds_budget(0, 0, FALLBACK_DEPTH + 1, false));
    }
}
