# R226 — Retain callback formal-use provenance

Status: CLOSED_PROVENANCE_METADATA; Luna solo primary, no subagents.
Baseline: `9429c1fbb` on `research/simple-sub-intrusion`.
Parent computation-forwarding theorem, R71 and R72 remain OPEN.

## Authority and boundary

R225's design-debt audit classifies the first missing fact as D: source collection has an authenticated formal registration for callback-body Apply `f z`, but its candidate-context source-origin record retains only the occurrence. R225 explicitly authorizes a bounded packet to preserve that existing identity and retry an owner-qualified route proof.

Retain a compact source index from the Apply occurrence to its existing formal registration. The candidate-context origin already retains that branded source occurrence, so the two records can be joined without copying the registration into every relation. Do not add an inference relation, alter term solving, change public APIs or language semantics, or claim this metadata alone closes the provider/formal bridge. Keep R71/R72 and the parent theorem OPEN. No subagents; no carryover.

## Target

For the R221 source, candidate source collection already records the callback Apply's `formal_name` and registration. Retain a compact, sorted occurrence-to-registration index in candidate call state and join it to the source-origin's exact HIR occurrence. The ordinary provider call `repeat loop` must retain no formal-use registration. Validate source artifact ownership and the exact registration; do not join by equal row/term IDs. Keep the existing all-call `by_occurrence` map scoped to scoped-experiment mode.

## Exact paths and checks

- `crates/yu-solver/src/candidate_call.rs`
- `crates/yu-solver/src/candidate_context_tests.rs`
- `crates/yu-solver/src/candidate_source.rs`
- `crates/yu-solver/src/lib.rs`
- `crates/yu-solver/src/candidate_scheme.rs`
- this contract
- `notes/theory/2026-10-21-r226-callback-formal-use-provenance.md`
- `tasks/agent-loop/current.json`

Run focused R226 and R225 tests, `cargo test -p yu-playground`, sprint check, 57 tooling tests, `git diff --check`, serialized state limit, then exact-path commit and push. 600 seconds. Solo primary; no independent review claimed.

## Closure condition

The exact callback source-origin joins to its formal registration through the authenticated compact index; the provider origin has none; ordinary candidate solve and playground tests pass. Record what typed bridge remains unproved. The parent theorem, R71 and R72 stay OPEN.

## Outcome

The ordinary candidate source path now retains a compact sorted occurrence-to-registration index for formal-name Apply calls. The R226 exact-source test confirms callback occurrence 19 resolves to its source registration while provider occurrence 26 has none. The provider argument relation and slot-4 result-effect edge remain proven only to the expected callback function; the typed route-to-WorkBound join remains OPEN. Focused R226, candidate-source tests, playground tests, sprint check, tooling tests, and diff checks passed. No inference behavior changed; R71, R72, and the parent theorem remain OPEN.
