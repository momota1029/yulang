# Copied Allowance activation: structural Value observation

Date: 2026-10-15
Status: reviewed bounded native observation; no H2/U or source-gate promotion
Baseline: `d8a6209c1dc181858948c4d811259aa20683d64e`
Branch: `research/simple-sub-intrusion`
Parent: every originally admitted shallow Catch under one original scoped
assignment; H1/H2/U OPEN; H3/P disabled; production/F5 separate

## Observation

The additive observer is
`crates/yu-solver/src/candidate_context_tests.rs::observe_structural_value_extrusion_current_and_late_allowance_pairs`.
It admits two distinct Allowance views over the same allowed operation, source
row and tail row; inserts a symbolic lower before copying; then drives a
positive structural Function-to-Value-row comparison through the normal typed
drain and `lib.rs` structural dispatch into `candidate_extrude`. It does not
manually enqueue the replay under investigation.

After the structural drain completes, the copied Function has a distinct
result-effect tail, and both original cuts have distinct copied Allowance
views on one copied source row. The original symbolic lower is retained on
that copied source. Each copied bound has two recorded origin entries. The
observer finds no `Replay` dependency pairing that copied lower with either
copied cut, and the completed drain leaves no queued Effect work. This records
an absent direct current-pair replay on this route; it does not establish that
a required source effect was lost or that no equivalent continuation already
exists.

As a later-lower control, the observer adds an unmatched operation contribution
directly to the copied source. Native replay dependencies reach both copied
cuts; drained Effect work reaches the copied tail, whose exact lower set
contains that contribution. This checks the later insertion route, not the
current symbolic-lower obligation.

The finite native fixture is not a source Catch construction and authenticates
no source profile, accepted source behavior, or source-qualified counterexample.
The parent H2 obligation therefore remains OPEN at the current copied symbolic
lower and its complete contextual continuation consequences before dependent
use/publication.

## Verification and review

Focused command:

```text
CARGO_BUILD_JOBS=2 timeout 300s cargo test -q -p yu-solver --features shadow-f5,shadow-apply-candidate --lib observe_structural_value_extrusion_current_and_late_allowance_pairs -- --nocapture --test-threads=1
```

One initial invocation failed to compile because the test attempted to read the
private effect-origin map. The test was repaired to use the existing
`candidate_bound_origin_count` accessor; the second invocation passed, with one
test run and 691 filtered out. `git diff --check` passed. No broad suite,
benchmark or other measurement ran; the preassigned two-invocation focused test
budget is fully consumed.

A fresh M2 `spec_auditor` reviewed the frozen test delta with no findings. The
review was limited to the selected native observer contract; it did not certify
source Catch reachability, H2/U, or production correctness. The paired
constructive derivation and falsifier were separately reviewed by a fresh M2
`compiler_referee` with no findings; they retain the atomic-factorization
premises and the unresolved symbolic/contextual activation bridge.

Commit packet: this note and the additive test delta only, plus synchronized
task/research records. No production inference code changed. Proposed message:
`test: observe current copied Allowance activation through Value dispatch`.
No theorem status or implementation authority follows.
