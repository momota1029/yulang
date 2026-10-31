# Frozen source handoff — EFFECT-PERMISSION-OBSERVER-EVIDENCE-REPAIR/R100

Assignment-ID / revision: `effect-permission-observer-evidence-repair` / 1.
Parent and prior evidence: R99 outcome `tasks/agent-loop/history/effect-permission-member-owner-repair-20261101-r99-outcome.md`; the observer candidate remains diagnostic/test-only and provisional. Parent theorem, source/native bridge, semantics and production gates remain OPEN.
Baseline / direct source hash: `crates/yu-solver/src/candidate_effect.rs` SHA-256 `bf7528133a1ebaa0a80434f2bf114d21c06717235575bab45fbf4c5dffc7cb57`.
Exact writable paths: `crates/yu-solver/src/candidate_effect.rs` and this handoff only. No descendants.
Requested model and effort / observed model and effort: Luna/high; observed model and effort UNKNOWN in this worker view.

## Source changes

At the protected nonrecursive test, preserved the `negative-root-publish` event prefix and exact domain/node adjacency while allowing the emitted `id=...` field between the prefix and `term=...`. The assertion still joins the exact `negative_term` parsed from `constructor-formal-domain-publish` to the published root's `node=` field.

At the symbolic memo observer test, indexed typed events and captured all `'e` memo observations. The test retains its unique-miss and minimum-hit assertions, identifies the unique miss, checks that its event index precedes every hit, and requires every hit's witness list to equal the miss's list exactly. Every delegated-tail witness list must also equal that same list exactly. Removed the prior tautological comparison that let each hit satisfy itself. The existing tail interning assertion now joins the canonical intern event to that same miss witness list and row. Kept the same constructor and row checks, delegated-tail count, fixtures, sibling paths, source-row and `SupportView` consumer assertions, and transaction assertions. Updated the delegated-port/tail comparison to use the unique memo miss row after indexing the memo tuples.

These are the two authorized assertion areas only. No emitter or production code changed.

## Checks and limits

Static inspection only. No Cargo/build/test, Git, scratch, environment change, or additional path write. No independent review or test execution is claimed. The original parent/source/native correspondence and every production gate remain OPEN. No syntax issue was identified by static inspection; execution remains NOT_RUN.

Final `candidate_effect.rs` SHA-256: `114bf61685037e65a7ff5ebb83e089080b7b38433472197eabe7ff1026e03cbc`.

All writes ceased before handoff hashing: **STOPPED**. No descendants or disposable scratch were created.
