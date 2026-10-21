# R280 — parse qualified constructor application in Yulang2 patterns

Status: CHECKPOINTED_UNREVIEWED; Luna-only serial implementation under the user's solo constraint.
Parent: unchanged Yulang2 Types/Console and broad playground sample goal under Authoritative R149.
Baseline: `d6c2c4914` on `research/simple-sub-intrusion`.
Authority: R149 unchanged-source requirement; exact pinned `std::core::fmt` bytes; the converted unified design and proof companion. The `[io]` contravariant open-row correction `[io,'e]` remains governing and is unrelated to this parser slice.

## Dispatch decision and source evidence

At the R279 boundary I applied the sprint selector's altitude/depth/range/falsifier check in the primary lane. The user-directed solo constraint rules out delegated dispatch. R279's exact pinned fmt diagnostics are 15 `CaseArm` missing slots paired with 15 `OperatorChain` errors, plus one root recovery and one `StringEscape` missing. Their ranges cluster at the arrow after forms such as `opt::just fill`, `std::data::list::list_view::leaf item`, and `result::ok inner`. A minimal CLI reproduction confirms that the parser leaves same-line payload patterns after qualified constructors unconsumed. Existing Pattern ML application is admitted through GML classification; plain `f x` already constructs a Pattern application node. The pinned qualified path plus same-line payload still fails because it is not recognized as a completed constructor receiver.

## Outcome

Recognize a same-line ML application of a `::`-qualified constructor path to its following payload Pattern in case arms, retaining existing path/call CST ownership and the caller's arrow boundary. Keep unqualified `f x` behavior, GML continuation rules, qualified nullary paths, parenthesized constructor arguments and malformed path recovery stable. Use the existing `PatternMlApplicationTail` representation unless a source-backed invariant requires a new node.

Expected exact fmt effect: remove the 15 arrow-frontier `CaseArm`/`OperatorChain` pairs without changing source bytes or unrelated diagnostic ranges. Preserve the remaining root `ErrorGroup` and `StringEscape` diagnosis for later owner routing.

## Falsifiers

A qualified path followed by one same-line binder still leaves the arrow pending; an unqualified same-line application changes; GML layout boundaries change; the application consumes the caller-owned arrow, guard, next arm or declaration; nullary paths or adjacent call patterns regress; exact pinned source bytes/identity change; unrelated diagnostics shift or multiply.

## Exact write paths

- `crates/yu-syntax/src/pattern/mod.rs`
- `crates/yu-syntax/src/tests/pattern.rs`
- `crates/yu-syntax/src/tests/case_like.rs` (only if the focused owner fixture belongs there)
- `tools/inference-playground/src/lib.rs` (exact fmt diagnostic partition)
- `notes/design/2026-10-22-r280-y2-qualified-constructor-pattern-application.md`
- `notes/theory/2026-10-22-r280-y2-qualified-constructor-pattern-application.md`
- `tasks/agent-loop/inbox/20261022-r280-y2-qualified-constructor-pattern-application.md`
- `tasks/agent-loop/sprints/r280-y2-qualified-constructor-pattern-application-20261022.md`
- `tasks/current.md`
- `tasks/agent-loop/current.json`

No additional writer or code owner is assigned. Stop at a cross-owner semantic seam and revise authority before editing it.

## Verification and resources

Focused Pattern and Case parsing/recovery tests, exact pinned fmt diagnostic partition, `cargo check -p yu-playground`, static sprint check and `git diff --check`. Do not run workspace-wide formatting/tests. One Cargo process at a time. Cap 900 seconds, no carryover. Solo primary checkpoint means independent review remains unavailable and every theorem/production gate stays open.

## Result

The case-arm PATTERN_STOP_ITEM guard previously blocked a constructor's same-line payload argument. The parser now admits one qualified-constructor Pattern application through that guard while preserving its PatternMlApplicationTail CST and returning the arm arrow to the case owner. The exact pinned fmt census is 2 diagnostics: one root ErrorGroup and one Missing/StringEscape; the 15 CaseArm and 15 OperatorChain diagnostics are gone. The remaining errors are both at source line 202 (x.debug = quoted string + x + quoted string), so they remain separately owned.

The focused qualified Pattern test, all 80 Pattern tests, all 34 case-like tests, exact pinned fmt census, cargo check -p yu-playground, static sprint check and diff check pass. User-directed solo work means independent review is unavailable. HIR traversal, roles, sample output, source/native proof and production remain OPEN.
