# R278 — Yulang2 dotted binding target in Pattern

Status: CHECKPOINTED_UNREVIEWED; solo primary implementation, no delegated workers.
Parent: unchanged Yulang2 Types/Console and broader playground sample goal under Authoritative R149.
Baseline: `0527c44ad` on `research/simple-sub-intrusion`.
Authority: R149 exact pinned `fmt.yu`; Yulang2 oracle source facts recorded in R149 evidence and the Chasa Role addendum; R89 syntax obstruction; R277 exact diagnostic census.

## Outcome

Implement the deferred Yulang2 Pattern continuation `IdentifierPattern` followed by adjacent `.field`, preserving the Y3 tree convention of separate `Dot` and `Identifier` tokens. Represent each continuation as a dedicated `PatternFieldTail`, parented to the same Pattern, with exact source ranges and recovery. Keep expression `FieldTail` and path `PatternPathTail` meanings distinct.

The source forms anchoring this work are the unchanged pinned `fmt.yu` role signature `pub a.show: str` and implementation target `our value.show = ...`. Add focused valid and malformed-neighbor tests, then re-run the exact pinned-source diagnostic census to measure the change.

Success evidence: adjacent identifier-dot-field chains appear as ordered parse-owned nodes; role-signature and implementation-target fixtures have no syntax errors at the target; spaced dots, bare dots, missing members, and longer competing tokens do not become valid field continuations or consume caller delimiters. The full fmt module may retain other diagnostics; this sprint does not claim module/HIR/sample support.

Falsifiers: any source byte is lost/reordered; `PatternFieldTail` accepts non-identifier receivers or non-adjacent dot/member tokens; recovery steals the next binding/body/close token; expression `FieldTail` behavior changes; the exact R149 target still fails at the dotted pattern.

## Parent and lanes

- Implementation: Luna owns syntax vocabulary, Pattern grammar and focused syntax fixtures.
- Proof: R149 source/native and the original Simple-sub A/B remain OPEN. This grammar fact is not a type-safety or role-selection theorem.
- Review: primary-only; no independent reviewer or subagent under the user-directed solo constraint. The checkpoint remains unreviewed.

## Exact write paths

- `crates/yu-syntax/src/syntax_kind.rs`
- `crates/yu-syntax/src/pattern/mod.rs`
- `crates/yu-syntax/src/tests/declaration/role_decl.rs`
- this contract
- `notes/design/2026-10-21-r278-y2-dotted-binding-pattern.md`
- `notes/theory/2026-10-21-r278-y2-dotted-pattern-target.md`
- `tasks/agent-loop/inbox/20261021-r278-y2-dotted-pattern-target.md`
- `tools/inference-playground/src/lib.rs` (pinned-source diagnostic baseline update only)
- `tasks/agent-loop/current.json`
- `tasks/current.md`

If the grammar requires edits outside these exact owners, stop before editing and issue a sequential lease revision.

## Verification and limits

Focused `yu-syntax` tests for exact role/impl target trees and malformed neighbors, the focused pinned `fmt.yu` diagnostic census, and `cargo check -p yu-playground` pass. Sprint static and diff checks run at close. No full workspace suite or sample success claim. Cap 600 seconds, no carryover.

## Non-goals

No role/member semantics, HIR module admission, imported constraints, lookup/selection, runtime, outputs, source/native proof closure, semantic change or production promotion. Preserve the open-row `[io,'e]` interpretation in contravariant `[io]` annotations.
