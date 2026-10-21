# R281 — parse escaped quotes in unchanged Yulang2 strings

Status: CHECKPOINTED_UNREVIEWED; Luna-only serial implementation under the user's solo constraint.
Parent: unchanged Yulang2 Types/Console and broad playground sample goal under Authoritative R149.
Baseline: `39de8f156` on `research/simple-sub-intrusion`.
Authority: R149 unchanged-source requirement; exact pinned `std::core::fmt` bytes; converted unified design and proof companion. The user correction that contravariant `[io]` means `[io,'e]` remains governing and must not be regressed.

## Dispatch decision and source evidence

At the R280 boundary, the primary applied the altitude/depth/range/falsifier check; the solo constraint rules out delegated dispatch. The exact pinned fmt census now has only two errors, both on line 202: `Missing/StringEscape` at byte 5800 and root `ErrorGroup` at 5801..5813. Source line 202 encodes a quote with a backslash inside each string, followed by that string’s closing quote. The literal parser currently treats any quote immediately after a backslash as a close sentinel; an existing recovery test deliberately preserves that choice when no later delimiter is present.

## Outcome

Recognize the source-supported escaped quote when a subsequent closing delimiter is present in the same quote run, so the pinned debug formatter string becomes one valid StringLiteral. Preserve the existing incomplete-escape recovery at a lone quote sentinel and EOF. Do not rewrite source bytes or change unrelated simple, unicode, heredoc, interpolation, fence, or quote-width behavior.

Success: the exact pinned fmt census has no syntax diagnostics, with source bytes/Git blob unchanged; focused tests prove both valid quote escape and the existing incomplete sentinel recovery.

## Falsifiers

The paired quote is still reported missing or closes the literal before its contents; lone backslash-quote sentinel recovery changes; closing quote is consumed as string content; a fence/EOF or heredoc boundary changes; unrelated literal tests or diagnostic ranges move; pinned source identity or bytes change.

## Exact write paths

- `crates/yu-syntax/src/literal/mod.rs`
- `crates/yu-syntax/src/tests/literal.rs`
- `tools/inference-playground/src/lib.rs` (exact pinned fmt partition)
- `notes/design/2026-10-22-r281-y2-escaped-quote-literal.md`
- `notes/theory/2026-10-22-r281-y2-escaped-quote-literal.md`
- `tasks/agent-loop/inbox/20261022-r281-y2-escaped-quote-literal.md`
- this contract, `tasks/current.md`, `tasks/agent-loop/current.json`

No other writer or code owner is assigned. Stop at a cross-owner semantic seam and revise the lease before editing it.

## Verification and resources

Focused literal tests including existing sentinel/fence recovery, exact pinned fmt census, `cargo check -p yu-playground`, static sprint check and `git diff --check`. One Cargo process at a time. Cap 900 seconds, no carryover. Independent review unavailable under the user's solo constraint; no theorem or production closure is inferred.

## Result

The normal-string escape owner now consumes the first quote as `StringEscapeSimple` when a second quote remains to close the string. A lone quote sentinel and EOF retain their prior recovery. The exact pinned fmt census is empty; the original pinned source bytes and Git blob are unchanged. The escaped-quote and sentinel tests, all 38 literal tests, all 12 string-literal recovery tests, the pinned fmt census, playground check, static sprint check and diff check pass. This parser checkpoint provides no HIR, sample output, source/native proof or production closure.
