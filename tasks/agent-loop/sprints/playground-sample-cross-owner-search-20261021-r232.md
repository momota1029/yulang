# R232 — Search accepted playground samples for cross-owner WorkBound

Status: CLOSED_SOURCE_NATIVE_EVIDENCE; Luna solo primary, no independent review.
Branch / baseline: `research/simple-sub-intrusion` / `a6e7a6cde`.
Parent: unchanged computation-forwarding theorem §§1, 6–7; R71/R72 remain OPEN.

## Fixed outcome

Use the four executable Yulang2 browser playground samples as an actual source corpus for R71's reachable cross-owner alias schedule. Require candidate inference acceptance, complete forest history, and exact ordered merge/WorkBound traces. Search for a raw item's representative changing before its later Work::Bound while the owner remains outside that representative class. The two intentionally diagnostic examples are excluded from the constructive corpus and remain covered by their existing CLI rejection tests.

## Exact lease and boundaries

- `crates/yu-solver/src/shadow_apply/local_source_observation.rs` — test-only corpus trace.
- `tasks/agent-loop/sprints/playground-sample-cross-owner-search-20261021-r232.md`
- `notes/theory/2026-10-21-r232-playground-sample-cross-owner-search.md`
- `tasks/agent-loop/current.json`

No production code, playground source, public test expectation, semantics or theorem premise changes. No subagents. This corpus search may locate an exact witness or sharpen the next missing source owner; a finite miss is not a language-wide absence result.

## Success and falsifiers

A hit requires an accepted exact sample whose ordered parent-write prefix aliases a raw WorkBound item before its event, while its owner stays outside that class, with the source physical slot and retained fiber relation joined. Test the captured fixed samples through ordinary `CandidateInference::solve`; do not infer source acceptance from sample filenames alone. A falsifier is missing sample-to-HIR source correspondence, incomplete alias history, WorkBound preceding the merge, or a sibling/raw-key mismatch.

## Checks/resources

The focused corpus test, `cargo test -p yu-playground`, sprint static check, all 57 sprint tooling tests, and `git diff --check` passed. Runtime was not precisely metered, so the 720-second cap is charged conservatively with no carryover. No production implementation is authorized.
