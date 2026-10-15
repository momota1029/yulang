# Playground computation-root source plans

Date: 2026-10-15
Branch: research/simple-sub-intrusion
Code baseline: `13a8e36eb595e97b5667230c7463fdb09aed67b8`
Status: bounded observational implementation complete and independently reviewed

## Result and authority

`yu-playground --intrusion` now consumes a borrowed source plan for each
explicit Computation formal. It reports the original definition/Lambda/formal,
annotation and outer-row positions, retained native parameter root and entry
row, exact resolved concrete members and optional symbolic variable. Value
formals have no explicit Computation-root plan. Nested callback rows are not
mistaken for the outer row; an empty outer row does not cap incoming effects.

Authority is the existing [research playground scope](../design/2026-10-04-inference-research-playgrounds.md),
[annotation integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
sections 1–1.1 and the [root source construction](../theory/2026-10-15-root-computation-profile-source-construction.md)
sections 2–4. This implements a static source supplier and an actual display
consumer. It changes no solver constraints, permission activation or handling.
Other supported annotation payloads are factual observations, not an extension
of the Int-fragment proof.

The sole native endpoint owner remains
`candidate_source::initialize_candidate_source_levels`: it verifies the
parameter recipe against the original formal, rejects an already initialized
root and installs its positive Parameter endpoint once. The candidate result
moves that inventory into private frozen storage. The new observer validates
HIR/source associations and root kind/polarity while borrowing these canonical
constructor outputs. It does not independently reconstruct row identity or
authenticate Function AE/RE, copied ports, Name/Delay/argument transport,
actual receivers, receipts or handler eligibility.

The renderer charges every inspected registration and concrete/symbolic member
to the existing shared work budget and writes through the existing atomic byte
cap. There is no new inference traversal, persistent map or copied permission
inventory; observation uses existing indexes and borrows the original row.

## Review and repairs

M2 used one implementation pass, independent compiler-referee and specification
reviews, one batched implementation repair, and a fresh compiler-referee delta
review. Final review has no findings. Public README prose was produced on its
own disjoint lease and included in specification/delta review.

Initial compilation exposed an incorrect `solved.shadow_fresh_capture` field
path. Semantic review found the underlying cause: CandidateInference never
populates that optional legacy capture, so merely adding `.data` would still
make every formal observation fail. The repair consumes the existing candidate
constructor invariant above, without enabling the legacy capture route or
adding redundant evidence storage.

Pre-write specification review approved replacing the newly introduced
same-kind sibling-root corruption assertion with wrong-kind/polarity controls.
The former promised independent reconstruction beyond this constructor-owned
observation contract. Source-parameter, role and missing-entry mismatch checks
remain. This was a causal contract correction, not an output-driven weakening.

Two initial nested-row test sources hit the existing negative concrete-row
preflight limit before observation. Their unchanged root-versus-nested
assertions now use the already supported double-argument polarity shape from
`candidate_formal_effect_polarity::double_argument_flip_admits_concrete_formal_rows`.
No compiler admission rule or existing test expectation changed. Fresh delta
review covered the fixture correction.

## Exact checks

All Cargo invocations were serialized with `CARGO_BUILD_JOBS=2` and a 180-second
timeout. Test commands used `-- --test-threads=1`.

| Command | Final result |
| --- | --- |
| `cargo test -q -p yu-solver --features shadow-apply-candidate --test candidate_computation_source_plan` | 5 passed |
| `cargo test -q -p yu-solver --features shadow-apply-candidate --lib computation_source_plan_rejects_contradictory_registration_associations` | 1 passed |
| `cargo test -q -p yu-solver --features shadow-apply-candidate --test candidate_computation_laziness` | 6 passed |
| `cargo test -q -p yu-playground --test cli` | 20 passed, including intrusion and atomic output-cap controls |
| `cargo check -q --workspace` | passed once, no warnings |
| `rustfmt --edition 2024 --check crates/yu-solver/tests/candidate_computation_source_plan.rs` | passed after formatting only the new file |
| `git diff --check` | passed |

The source-plan test target had three total invocations: initial compile
failure; 3 passes/2 unsupported fixture failures; final 5 passes. All other
listed Cargo checks ran once. The initial new-file formatting check reported
format differences; only that new file was formatted. No broad workspace test,
whole-tree formatter, Oracle execution or benchmark ran. Performance samples
and benchmark processes: 0. Existing unrelated Effect fixture failures were
not rerun or changed by this slice.

Three direct `target/debug/yu-playground --intrusion -` executions, each with a
20-second subprocess bound, succeeded for `[io]`, `[]`, and an ordinary Value
formal. They produced one, one and zero static plans respectively. Source and
output conditions were checked by a short Python subprocess driver; logs are
in `/tmp/yulang-rootcomp-cli-vaj22pbr`. These execute inference/reporting, not
the Yulang program.

## Proof application and remaining work

Commit `13e9448c6` separately integrates the independently reviewed
[first-use FreshUse admission bridge](../theory/2026-10-15-computation-freshuse-admission-bridge.md).
It proves actual capture/restoration before publication for an isolated
first-use direct-Name Computation provider, followed by the conditional actual
Function/Apply scalar inclusion. The original general bridge remains OPEN for
signed copied/merged providers and later recapture. Twelve pinned dependency
hashes and local links were checked for that proof; no compiler execution was
used to claim theorem closure.

This playground slice supplies the explicit source annotation output. Its
next correspondence owner is the actual argument Name/registration route and
the receiving Function ports, then source-qualified capture/copy transport.
`ApplySourceInput.formal_name` identifies a formal used as callee and cannot
serve as the argument-Name supplier. Dynamic receiving views, read/Force,
expiry/reentry, selective Catch, full soundness/principality and native program
execution remain OPEN. H3/P are not enabled.

Task/research/index records are synchronized. The separately reviewed unary
lambda parser proposal awaits explicit user approval; its pending question
directory is excluded from this checkpoint. No parser implementation is
authorized by this observational change.
