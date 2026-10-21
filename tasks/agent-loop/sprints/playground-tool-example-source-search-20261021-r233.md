# R233 — Search inference-playground source examples for cross-owner WorkBound

Status: CLOSED_SOURCE_NATIVE_EVIDENCE; Luna solo primary, no independent review.
Branch / baseline: `research/simple-sub-intrusion` / `3363d98c7`.
Parent: unchanged computation-forwarding theorem §§1, 6–7; R71/R72 remain OPEN.

## Fixed outcome

Expand the source input beyond the four web samples to the checked-in `.yu` examples shipped with `tools/inference-playground`. Run each exact file through parse/lower and ordinary `CandidateInference::solve`; keep only cleanly accepted candidates for alias-prefix analysis. For every effect WorkBound, compare its raw owner/item at that exact prefix of the complete effect-row parent-write history. Search for a post-alias item whose owner remains outside its alias class.

This is a finite source corpus search. A hit must be joined to its exact source owner and retained physical fiber before it can answer R71; a miss cannot establish general source unreachability.

## Exact lease and boundaries

- `crates/yu-solver/src/shadow_apply/local_source_observation.rs` — test-only fixture corpus trace.
- `tasks/agent-loop/sprints/playground-tool-example-source-search-20261021-r233.md`
- `notes/theory/2026-10-21-r233-playground-tool-example-source-search.md`
- `tasks/agent-loop/current.json`

No production/sample edits or semantic/expected-output changes. No subagents. Keep rejected/unsupported examples visible as separate counts. The existing ordinary CLI package tests remain the runtime/example acceptance evidence.

## Success and falsifiers

A candidate hit requires an actual checked-in source file, clean candidate acceptance, complete forest history, an ordered alias write before WorkBound, changed item representative, distinct owner representative, and source/physical-fiber correspondence. Falsifiers: alias after WorkBound, item not changed, owner in same class, incomplete history, or absent source fiber. Do not infer a required consumer solely from a WorkBound hit.

## Checks/resources

The focused 20-example corpus test, `cargo test -p yu-playground`, sprint static check, all 57 tooling tests and `git diff --check` passed. Runtime was not precisely metered; the full 720-second cap is charged conservatively with no carryover. No production implementation is authorized.
