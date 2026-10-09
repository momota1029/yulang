# Candidate preflight no longer builds a discarded observer Call inventory

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Baseline: `f3a5a7e50bed3dedb45c822301bc67564f97423c`
Status: bounded retirement verified and reviewed
Authority: active Simple-sub legacy withdrawal; genuine Call owner retained
Mode: M1; independent regression review and fresh narrow delta review
Measurement consumed: zero timing samples / zero benchmark processes

## Actual dependency removed

`CandidateInference::solve` allocated a `Vec<CandidateCall>` for expression
preflight. Every Apply reserved capacity and cloned three occurrences; the
candidate discarded that inventory after validation. A reservation failure
could reject inference even though the inventory had no consumer. Actual
constraint recipes and graph execution already owned candidate solving;
LocalSource's genuine `candidate_call` table owns retained source Call inputs.

Preflight now accepts a validation-only mode with no inventory sink. All
expression-shape, scope, error and depth checks remain. The historical
`CandidateValueObservation` passes its real sink and retains ordering, cloned
identities, reserve failures, `calls()` and `apply_fact()`. Historical local
binding inventory construction keeps the same real owner. No source validation
or full Call requirement is retired by this allocation removal.

## Verification and adjudication

The new TLS failure probe establishes candidate success while the unused
inventory reservation failure remains armed, historical observer failure and
consumption, and successful retry with its real Call/Apply fact. A panic guard
clears the probe. The expression-backed fixture exercises the actual affected
preflight. Its exact exported Integer result is inspected through its own
reachable Value bounds. A separate LocalSource fixture preserves its actual
source Call observation.

Initial independent review found one major in the new test: expression-only
lowering has no LocalSource Call input carrier, so its expected source Call
count of one was a false fixture premise. The primary reproduced that failure.
Pre-write conformance review confirmed the source owner distinction. A fresh
test-only repair checks the expression export and the separate authentic
LocalSource inventory without altering production code or historical tests.
Fresh independent delta review found no findings.

Primary Cargo controls: `RUSTC_WRAPPER= timeout 180`, `-j 2 --offline`, tests
`-- --test-threads=1`. Focused commands, all with
`--features shadow-f5,shadow-apply-candidate`:

- `cargo test -p yu-solver --lib candidate_inference_does_not_reserve_historical_call_inventory`: 1 pass after the fixture repair.
- `cargo test -p yu-solver --lib preflight_depth_counts`: 2 pass; old collecting assertions retained and validation-only 128/129 boundaries added.
- `cargo test -p yu-solver --lib candidate_graph_call`: 2 pass.
- `cargo test -p yu-solver --test shadow_apply_candidate`: 19 pass as part of the explicit focused matrix.

Total: 24 distinct owning regressions. Owning all-target/all-feature checks,
workspace all-feature check and default checks pass without warnings at the
coherent annotated-formal/retirement phase boundary. No broad runtime suite,
benchmark, semantic theorem or target cutover is certified. Cost removed is the
extra observer Vec and occurrence clones; validation traversal is unchanged.

## Remaining migration

The historical observer retains real users and is not deleted. Default F5,
independent public schemes and full Call/hygiene/soundness/principality remain
active migration requirements. Source Call observations remain limited to their
actual LocalSource owner; this retirement does not fabricate them for fallback
expression recipes. Pending questions stay excluded from integration.
