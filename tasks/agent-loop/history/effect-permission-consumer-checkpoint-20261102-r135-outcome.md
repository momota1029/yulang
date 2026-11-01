# R135 outcome — reviewed permission receiver checkpoint

Status: `CLOSED_CONDITIONAL_NO_SAFE_CODE_SLICE`. The exact receiver research
checkpoint is pushed; further work in this effect component is waiting on new
source/proof evidence. The fixed Yulang soundness, original Simple-sub A/B and
effect-hygiene goal remains open.

## Before and after

At R135 baseline, committed `candidate_receiver.rs` was byte-identical to the
R111 target (`3ec1a45f…25cf`). R117 and corrected R119 patches had an
independently reviewed ordered composition at R127, but no newer checkpoint had
revalidated the receiver against the current committed APIs.

R135 reconstructed the same exact 296,602-byte target in memory, independently
reviewed it, and pushed only
`crates/yu-solver/src/candidate_receiver.rs` plus its review and policy records.
The target SHA-256 is
`335f5f2cd4841dd8288306623ee863606e355b9ceda6948ab6877d944bed3165`.
The normal push is `00b69295d`; current-state receipt is `543afdcdd`.
HEAD and origin were equal after push. R134's committed trace instrumentation
was confirmed not to change receiver APIs.

The implementation preserves distinct registration, packed permission slot,
native member and concrete permission-vector indices. It uniquely resolves the
retained registration, captures the first matching concrete family position,
transports that index with the same permission reference into the request, and
uses bounded `.get(index)` at the receiver. Existing optional failure and
fallback paths remain in use.

## Independent review and limits

Fresh compiler-referee review PASS; exact target and dependency pins matched.
The reviewer confirmed that for `[4,9,9]`, changing captured index 1 to 2 would
pass the local equality check. Correctness evidence is the source-level
`.position` plus unchanged index transport, not arbitrary in-memory tamper
detection. Static inspection proves neither compilation nor runtime
reachability, full vector provenance from pointer equality, Rust-to-Lean
correspondence, A/B closure, effect hygiene or production readiness.

No compiler, Cargo, tests, Lean, checker, scratch, environment/storage probe or
quarantined-path inspection occurred. R111's private compile/resource gate
remains unmet and unspent. Dirty `candidate_effect.rs`, `candidate_scheme.rs`,
`shadow_apply.rs`, quarantined runtime files, and pending R103/supplier artifacts
remain untouched and unstaged.

## Owner-specific next-step adjudication

The existing dispatcher inspected three approved committed owners at HEAD and
found no further safe code slice under unchanged inputs:

- `candidate_effect::candidate_formal_entry_annotation` preserves ordered
  concrete annotations and checks exact Lambda/formal; no new repair owner was
  identified.
- `candidate_receiver::internal_root_view_from` now carries the retained
  indexed family path. The duplicate-family example does not refute the required
  unchanged first-position transport and does not justify another guard.
- The committed `candidate_scheme` adapter matches session-owned route/origin/
  recipe/source Lambda and row views, but has no receiver consumer. Connecting
  it without a source judgment or consumer correspondence would be unsupported.

Implementation is `WAITING / NO_SAFE_CODE_SLICE`; proof is `WAITING` because an
authenticated relation from actual Rust vector/index/family evaluation to the
Lean indexed-read equation is absent. R104's four protected failures, original
A/B, source-to-Lean, effect-hygiene and production obligations remain OPEN.

Re-enter this component only with a new source law, an execution-derived
counterexample that changes the judgment, or an authorized verifier resource;
otherwise select a distinct original parent obligation with concrete frozen
inputs. No further workers, leases or execution resources are admitted here.
