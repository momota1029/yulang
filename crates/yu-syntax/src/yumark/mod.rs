//! Isolated Yumark Gate 2 judges and Gate 3 structural grammar.
//!
//! Gate 3 is the single iterative decision driver selected by §§4, 5, 7–9 and
//! 11 of the authoritative doc-comment addendum. It reports structure through
//! the crate-private [`grammar::Sink`] callback contract:
//!
//! - `Enter(kind)` opens one structural node;
//! - `Token(kind, range)` assigns exactly that source byte range to one token;
//! - `Exit` closes the most recent unmatched `Enter`;
//! - `Recovery(kind/slot, range)` reports one §8/§9 typed recovery occurrence.
//!
//! Ranges are half-open byte ranges into the original source. The driver never
//! stores this stream. Only the test recording sink collects it in a `Vec`;
//! Gate 5 adds the isolated streaming AST/direct sinks in [`adapter`] without
//! adding another grammar or scanner. Sink checkpoints are control operations required by §4 transaction
//! rollback and by post-group link/apply classification; they add no fifth
//! event kind and retain no production event buffer.
//!
//! A fence selected by the parsed-Yulang-fence addendum emits its opener, info,
//! opening newline, and close/recovery boundary facts here, but no body event.
//! Its `YmYulangCodeCell` body remains deferred to that addendum's §7 Yumark
//! convergence gate. Every non-selected fence emits one source-range
//! `YmCodeFenceText` token in this gate.
//!
//! The later T2a evidence-timing correction defers the T2 embedded AST/direct
//! equality and Gate-3 completion certification to O6 (its §2 lines 88–107 and
//! §3 lines 125–137). This module fabricates no embedded fact, assigns no
//! frame-pop credit, and does not alter Yumark recovery transport for T2.
//!
//! There is deliberately no root, Statement, header, or public parser dispatch
//! edge in this module.

#![allow(
    dead_code,
    reason = "Gate 2 is an isolated construction; production dispatch belongs to Gate 6"
)]

mod adapter;
mod frame;
mod grammar;
mod judge;
