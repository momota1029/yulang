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
//!
//! ## Static performance ledger (Gate 7)
//!
//! - Judges inspect only the current marker, chunk, or physical line. Their
//!   time is linear in the bytes they settle and their retained memory is
//!   `O(1)`; they neither rescan a body nor duplicate the canonical scanner.
//!   `tests::doc_comment_matrix::public_deep_frame_matrix_is_iterative_and_linear`
//!   pins the public byte ledger, while `judge::tests` pins neutral probes.
//! - [`frame`] uses the persistent frame chain selected by the transaction
//!   amendment. Push/pop/checkpoint are `O(1)`, retained memory is
//!   `O(current structural nesting + live checkpoint heads)`, and unique-chain
//!   release is iterative rather than public recursion. The public deep-frame
//!   matrix above covers sections, lists, quotes, groups, and commands.
//! - [`grammar`] is one forward iterative driver: `O(bytes + structural nodes
//!   + embedded work)` time and `O(structural nesting)` working memory. It has
//!   no opaque full-body call, event replay, or recursive public parse. The
//!   public form/recovery matrices and the exact `byte_visits == body.len()`
//!   deep rows pin those claims.
//! - [`adapter`] adds `O(1)` work per streamed event. The direct adapter writes
//!   the caller's Rowan output and does not allocate an AST mirror; the AST
//!   adapter alone owns structural vectors. The public root output constructs
//!   completed green children bottom-up without Rowan's recursive node-cache
//!   hash, so it is `O(nodes)` product memory with no subtree rescan. Products
//!   deeper than the guarded threshold are also released by one iterative
//!   `O(nodes)` walk rather than recursive green-node destruction.
//!   `adapter::tests::static_driver_evidence_has_no_opaque_scan_replay_or_ast_in_direct_sink`
//!   guards the forbidden calls, and the public topology and deep-frame
//!   matrices pin direct child order, construction, and teardown.
//! - The embedded-Yulang bridge invokes the existing canonical owner once in
//!   its borrowed delimiter home. Its cost is the canonical payload work plus
//!   `O(1)` boundary/frame state; it has no nested `Root`, public entrypoint,
//!   replay, or second scanner. The public embedded-delimiter rows pin the
//!   adapter homes and local recovery, and the deep command byte ledger rules
//!   out byte multiplication. Selected `yulang` fence bodies remain deferred
//!   as stated above, so this ledger claims boundary-only work for them.

#![allow(
    dead_code,
    reason = "Gate 2 is an isolated construction; production dispatch belongs to Gate 6"
)]

pub(crate) mod adapter;
mod frame;
mod grammar;
pub(crate) mod judge;
