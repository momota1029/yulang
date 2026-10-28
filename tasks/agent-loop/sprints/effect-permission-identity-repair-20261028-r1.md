# Sprint EFFECT-PERMISSION-IDENTITY-REPAIR-20261028/r1

Status: CANDIDATE pending primary admission. The unchanged goal remains Yulang
type-inference and executor soundness, especially effect hygiene.

Branch `yulang3`; committed baseline `29b85224b` plus the exact frozen working
tree overlay listed below. The overlay is candidate research instrumentation,
not integrated/accepted source; retain every hash before re-lease.

## Outcome, semantics and success

Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
§§1, 3, 5, with original quantifiers and source domain intact. Preserve
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–5:
contravariant `[E]` grants local subtraction permission, only actual handler
inflow is subtracted, symbolic dependencies remain, and independent same-row
lineages remain distinct. No source restriction, solver/preflight/recovery/API
change, semantic change, expected-output change or production approval.

The decisive outcome is to carry the same allocated-row witness through
canonical capture into the exact owner's exported permission port. Repair both
known build blockers: the test-only `Graph` field initialization and Lean
indexed-case binders. Strengthen the owner/capture relation beyond membership
of a port in the same graph. Reuse the exact checked 12-theorem SourceOrigin
result; do not add a new abstract model for that layer.

Success: candidate Rust source compiles with the required feature, the ordinary
source-approved test observes the same constructor row, capture identity,
canonical endpoint/node and exact owner export; all 11 extension declarations
receive final-hash theorem type and transitive axiom audits; a fresh reviewer
confirms no goal conclusion was assumed. An exact first source/native transition
that remains unsupported is acceptable only as an explicit open bridge with
strongest prior evidence. A source-approved successful export that disagrees
with the same occurrence/path/row witness falsifies the proposed relation.
Passing tests alone prove no universal theorem.

## Exact overlay and dependencies

Committed baseline: `29b85224b`. Frozen candidate overlay:

- `candidate_effect.rs`: `f7dd1d1bf1e66e98d969aa9f7cadc1faad4c1325acf65e8d9da56e2593a84bec`
- `candidate_scheme.rs`: `0c3d87610452f78f27189d0f6554d52d9422e2fcc2a4d38d93014538002553a4`
- failed `FormalPermissionConstructorRealization.lean`:
  `893dcc04d23491b64230a2ebad956c3da88eb3e8b6146479a4aa616abc5f2e58`
- checked read-only `FormalPermissionSourceOrigin.lean`:
  `db37f9d83e450a450d689b9eed46311108e635eb846d268b7a3a567dcee624fd`

Other pins: `shadow_apply.rs`
`2e0aba4d172e97dd60ba909a7aca873c109785f3d38cce46ddd033c70f64613d`;
`yu-solver/Cargo.toml`
`aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`;
correct Lean manifest
`058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`;
Lean 4.35.0 toolchain, lakefile, authority, inference principles, parent and
prior module pins are in the preceding contract and outcome. No dependency
change is allowed.

## Rust lane — Luna/high `implementer`

Write leases: `crates/yu-solver/src/candidate_effect.rs`,
`crates/yu-solver/src/candidate_scheme.rs`, and
`crates/yu-solver/src/shadow_apply.rs`, the last limited to the two exhaustive
test `Graph` literals that omit `formal_capture_trace_id` and directly needed
test trace integration. New handoff:
`tasks/agent-loop/inbox/effect-permission-identity-repair-rust.md`.
Scratch only:
`/tmp/yulang-effect-permission-identity-repair-20261028-r1/rust-target/`.

First fix both `Graph` literals or redesign identity placement without adding
uninitialized required fields. Strengthen test-only events/assertions so one
captured witness joins constructor allocation, memo key, delegated allocations,
original occurrence/path, canonical Effect endpoint, interned node index,
capture id, graph root and the exact owner's actual exported port. Do not accept
graph membership alone. Exercise only ordinary source preflight/solve/export;
never bypass refusal. Keep instrumentation `#[cfg(test)]`, lazy and dormant
when disabled. No solver behavior, semantics, API, recovery or outputs change.

The previous command omitted the required feature and executed zero tests.
Freeze the corrected exact argv before the only Cargo invocation, including
`--features shadow-apply-candidate`. Retain raw stdout/stderr, argv, final
source/dependency hashes, exit status, time/RSS/CPU and launch headroom under
the scratch lease and handoff. One CPU, >=4 GiB available at launch, <=2 GiB
RSS, <=180 seconds. No retry. Resolve `Graph` constructor compatibility before
using the one invocation.

## Lean lane — registered `lean_prover`

Write lease only: `notes/theory/lean/YulangClosure/FormalPermissionConstructorRealization.lean`
and `tasks/agent-loop/inbox/effect-permission-identity-repair-proof.md`.
Read-only exact pin: repaired SourceOrigin
`db37f9d83e450a450d689b9eed46311108e635eb846d268b7a3a567dcee624fd`, whose 12
types and axioms already passed invocation 1. Scratch only:
`/tmp/yulang-effect-permission-identity-repair-20261028-r1/lean-project/`.

Preserve the exact prior failed source/logs before editing. Repair the indexed
case binder lists using actual recursor signatures. Audit all 11 extension
declarations on final bytes, including complete theorem types and transitive
axioms. Reuse (do not reconstruct or overclaim) SourceOrigin's prior 12-audit
receipt. Apply the checked event result to the same-witness source observation;
keep native successful-constructor exhaustiveness, allocated row/view/bound
decoding, row indexing, canonical transport, capture recurrence and export
membership explicit wherever still open.

At most three serialized Lean/helper invocations total, sharing <=180 seconds;
one CPU, <=1 GiB RSS per process. A later attempt requires both a diagnosed
failure and changed source. Preserve failures; no further invocation after
three. No default/root integration.

## Review, envelope and stop

After both lanes freeze, assign a fresh non-author read-only
`compiler_referee`. Review feature-correct compilation, both test constructors,
owner-specific witness identity, actual source path, the exact 11 theorem and
axiom audits, and whether the proof event decoder assumes its conclusion.
Preserve the known native/model boundary.

Total: **1,800 seconds** — Rust 600, Lean 600, review 300, primary 150,
dispatcher 50, contingency 100. At most two producers, zero Astra. Serialize
heavy checks. Only Luna updates current state, adjudicates, stages exact paths,
commits and pushes. Stop on changed pins, another owner, source refusal,
unsupported correspondence, falsifier, resource or invocation budget. All
parent, effect-hygiene, A/B, principality, termination, native and production
gates remain OPEN.
