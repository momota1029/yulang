# R234 — Search handler/recursion source schedules for cross-owner WorkBound

Status: CLOSED_SOURCE_NATIVE_EVIDENCE; Luna solo primary, no independent review.
Branch / baseline: `research/simple-sub-intrusion` / `2b21b1df7`.
Parent: unchanged computation-forwarding theorem §§1, 6–7; R71/R72 remain OPEN.

## Fixed outcome

Change the source family after the R221 call-placement and checked-in-example searches found no target. Starting from the admitted recursive callback fixture, place ordinary shallow operation handlers around the recursive call, helper call, callback invocation and provider call; also test a direct operation-producing recursive body. Determine whether these source constructors create a third-owner effect item alias followed by a later Work::Bound selecting that raw item.

Require parse/lower correctness, ordinary candidate acceptance, complete alias history, exact ordered row merges and WorkBound raw keys. A bounded hit must then be joined to source physical admission/fiber and the exact consumer; a miss stays case-specific.

## Exact lease and boundaries

- `crates/yu-solver/src/shadow_apply/local_source_observation.rs` — `#[cfg(test)]` source probe.
- `tasks/agent-loop/sprints/handler-recursion-source-search-20261021-r234.md`
- `notes/theory/2026-10-21-r234-handler-recursion-source-search.md`
- `tasks/agent-loop/current.json`

No production or playground sample edits, semantics, or expected-output changes. No subagents. Rejected candidates remain recorded and do not count as absence evidence.

## Success/falsifiers and checks

A hit needs an accepted ordinary source whose physical raw item is aliased by an ordered row merge before a later WorkBound, with the owner outside the item class and exact source/fiber/consumer ownership. Falsifiers include WorkBound before merge, item unchanged, owner merged, or missing source relation. A finite miss is not general impossibility.

Run results:

- Focused handler-family test: passed, 5/5 source variants accepted; no cross-owner alias hit.
- `cargo test -p yu-playground`: passed.
- `python3 tools/agent_sprint.py check`: passed.
- `python3 -m unittest discover -s tools -p 'test_agent_sprint.py'`: passed (57 tests).
- `git diff --check`: passed.

Outcome archive: `notes/theory/2026-10-21-r234-handler-recursion-source-search.md`. Budget cap 720 seconds, no carryover. No production implementation is authorized.
