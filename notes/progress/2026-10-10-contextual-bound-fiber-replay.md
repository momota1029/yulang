# Contextual bound fibers and replay scheduling checkpoint (2026-10-10)

Status: reviewed implementation checkpoint; partial Authoritative contextual
attachment gate
Baseline: `bb05dea3561aab837b6a0c69e8e8465fd8c26cfc`
Authority: `notes/design/2026-10-10-contextual-attachment-admission-design.md` §§3–4

The private Simple-sub contextual relation store now retains multiple exact
context fibers for one bound. Bound chains and replay frontiers participate in
route rollback and retained-capacity accounting. Capture and transport preserve
all fibers. Transport retains provenance without creating a fresh-use conflict
edge; same-owner representative migration retains the derivation edge.

Opposite-bound replay now retains ordered lower/upper context pairs and both
parent dependencies. Ordinary propagation visits only newly formed fiber
pairs. An incoming scheme restoration replays every applicable pair again so
diagnostics retain that use's occurrence and cause. Replay output storage stays
charged as scratch through queue publication and nested execution, including
the failure path. Representative changes also transport incoming third-owner
fibers to canonical bound keys before later replay; restoration canonicalizes
the owner, inserted bound, and opposite endpoint consistently.

An initial independent review found loss of third-owner bounds after
representative changes and unaccounted/repeated Cartesian replay work. The
batched repair was reviewed by fresh compiler-referee, spec-auditor, and
performance-auditor passes. The subsequent delta exposed and repaired stale
representative lookup on later restoration and missing diagnostics on repeated
restoration under a new use cause. Final fresh reviews found no actionable
findings in this slice.

Focused verification passed:

- `RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_context::tests --offline --jobs=1 -- --test-threads=1` — 22 tests.
- The same command with `candidate_effect::tests` — 27 tests.
- The same command with `candidate_intrusion::tests` — 5 tests.
- `git diff --check`.

No timing measurement or broad suite ran. Static cost for incremental
propagation is O(L×U) across a fixed lower/upper fiber product; incoming-use
diagnostic replay intentionally costs O(L×U) per restoration. Replay output
capacity is charged while live. Linear duplicate scans per bound attachment
and scans of retained bounds on representative merges remain explicit cost
risks without input-scale evidence.

This checkpoint does not implement PUSH/POP/SWAP/BOTH evaluation, source
operation payload construction, general contextual execution, freshening of
operation payloads, the certified-cycle invalidation lifecycle, or arbitrary
formal-row admission. Operation-bearing replay remains unavailable in the
private candidate. Default/public routing, ordinary inference, complete Call,
effect hygiene, soundness/principality and F5 retirement remain open. The full
user objective remains active.
