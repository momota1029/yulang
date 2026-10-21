# Sprint R206 — Origin completion and local-expression join

Status: ACTIVE, primary-only exact readback.

## Goal

Continue the user's original inference-proof goal by resolving the two remaining factual gaps from R205: whether Origin 31/32's separate source-drain completion records exist, and which local source form owns occurrence 15. Preserve R183's original quantifiers and open status.

## Exact authority

Baseline `76b3a628a` plus the R205 test-only observation on the shared branch. Read the R183 frozen contract/result and R205 note. Exact editable files: this contract, `crates/yu-solver/src/shadow_apply/local_source_observation.rs` (test-only query output), `notes/theory/2026-10-21-r206-source-origin-completion.md`, and `tasks/agent-loop/current.json`. No production changes, no subagents, no edits to frozen R183 artifacts.

## Validation

One targeted `yu-solver` test process maximum, with output under `target/r206-source-origin/`; no retry. Add only reads of `source_drain_completed(receipt)` and the existing HIR local expression form keyed by the retained occurrence. Remove scratch at closeout. This is fixture evidence, not theorem closure.

## Outcome

Name the exact source expressions and completed status for relations 56/57, or record the first unavailable field. Separate those source-origin rows from relation 62's event-1 occurrence and relation 53's FreshUse antecedent. State exactly what remains to establish an actual same-provider source-to-Capture path.
