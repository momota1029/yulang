# Sprint EFFECT-PERMISSION-EXPORT-WITNESS-20261028/r1

Status: ADMITTED by Luna after verifying the exact overlay and contract hash;
the admission and leases are recorded in `current.json`. This continues the user's
unchanged Yulang inference/executor soundness goal, especially effect hygiene.

Branch `yulang3`; committed baseline `43b06a4a3` plus the exact Rust overlay
below. The overlay is a provisional research instrument, not production source.

## Original obligation, semantics and outcome

Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
§§1, 3, 5, with its original quantifiers and source domain unchanged. Preserve
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–5:
contravariant `[E]` grants local subtraction permission, only actual handler
inflow is subtracted, symbolic dependencies remain, and independent same-row
lineages remain distinct. No source restriction, semantics, solver/preflight/
recovery/API change, expected-output change or production approval.

Prior bounded result:
`tasks/agent-loop/history/effect-permission-identity-repair-20261028-r1-outcome.md`, SHA-256
`b48182e1f612ccd87c13c22ec6d3c622c15a0c03e44902adb55293af075c611c`.
Independent review:
`tasks/agent-loop/inbox/effect-permission-identity-repair-review.md`, SHA-256
`22ad978a5c1907d11ebe7434f77406c76f98bcc67c43da4e77d83e1a7844e5f8`.
The user-owned objective remains ACTIVE; this contract does not promote a
parent or native theorem.

Decisive outcome: for **every** ordinary source-approved constructor permission
origin, connect the original allocation row `r`, source occurrence and complete
path to the canonical capture-time representative `q`, interned polarized
Effect node, and the exact returned permission port in that owner's export.
Connect both delegated signature-port allocations separately from the
symbolic tail. Preserve `r → q` even when `r != q`; preserve distinct origins
even when they share a numeric row. Use typed test-only identities; debug text
is diagnostic only.

Success is one focused, feature-correct source test invocation in which both
existing focused cases pass and reject all four logical mutations: wrong owner
wrapper, omitted second origin, swapped sibling exported ports, and lost or
incorrect `r → q` transport. The successful observation must check the exact
parameter-base offset equation and both delegated port allocations. Also check
a Lean decoder/instantiation for the recorded constructor-to-event-history
relation on final bytes, with all assumptions explicit and no goal conclusion
assumed. A first unsupported source/native transition may remain open only if
the maximal prior evidence and exact next owner are stated. Tests and event
history do not close the original universal theorem.

Falsifiers include a successful ordinary export assigning an origin to a
different owner, occurrence, path, representative, polarized node or returned
port; a duplicate/sibling lineage swap; a missed successful delegated port; or
a Lean decoder that accepts any of the four mutated records. Source/native,
parent, effect-hygiene, A/B, principality, termination and production gates
remain OPEN unless independently discharged by their governing obligations.

## Frozen baseline and dependencies

Committed baseline: `43b06a4a3`. Rust candidate overlay at admission:

- `crates/yu-solver/src/candidate_effect.rs`:
  `85d624cd2a1c5b4f821b58aa30f4dbf4fb59c1f4c9650f88b51382c07cc95d3a`
- `crates/yu-solver/src/candidate_scheme.rs`:
  `9eaee3528f36fcac180fe3b0e0428c8f353c2911fb0b854e621e57e08720e4d7`
- read-only `crates/yu-solver/src/shadow_apply.rs`:
  `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`
- `crates/yu-solver/Cargo.toml`:
  `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`
- checked read-only `FormalPermissionSourceOrigin.lean`:
  `db37f9d83e450a450d689b9eed46311108e635eb846d268b7a3a567dcee624fd`
- checked read-only `FormalPermissionConstructorRealization.lean`:
  `70a89e7ea4589951e5f5e9323b4b2b415003c5868dc3f53ce16129fa67eafdd9`

The previous frozen Cargo failure logs and argv stay in
`/tmp/yulang-effect-permission-identity-repair-20261028-r1/rust-target/` and
must be retained. No dependency change is authorized.

Exact scratch leases for this sprint:

- Rust target tree and argv/input/raw-log/resource receipts:
  `/tmp/yulang-effect-permission-export-witness-20261028-r1/rust-target/`
- Lean project copy, generated outputs, helper scripts and all check/audit logs:
  `/tmp/yulang-effect-permission-export-witness-20261028-r1/lean-project/`

No other scratch path is leased. Keep the existing identity-repair logs intact.

## Continuing implementation lane — Luna/high

Write leases, the two existing focused tests and their direct test-only
recorder:

- `crates/yu-solver/src/candidate_effect.rs`
- `crates/yu-solver/src/candidate_scheme.rs`
- `tasks/agent-loop/inbox/effect-permission-export-witness-rust.md`

Read-only inputs: `shadow_apply.rs`, current `yu-solver/Cargo.toml`, the two
checked Lean modules, and the exact review/outcome receipts above. Do not edit
`shadow_apply.rs` unless a concrete need is returned to Luna for a versioned
contract amendment and non-overlapping lease. No other repository source path.

Replace textual event matching with typed `SourceRootId`, occurrence, row and
complete-path fields. Retain original row `r` before canonicalization and
capture-time representative `q` afterward, with an explicit identity relation;
do not require numeric equality. Match every captured origin against its
owner's actual exported permission metadata, full path, endpoint polarity,
interned node and returned port. Compare intern/export node indices. Include the
second origin and adversarial swapped-port assertion. Record successful
delegated signature Effect-port allocations and their order separately from
the delegated symbolic tail. Assert the exact parameter-row offset equation.
Keep all recorder logic `#[cfg(test)]`, dormant when disabled and formatting
lazy. Preserve ordinary `CandidateInference::solve`, source preflight,
recovery, production behavior, outputs, tests outside the two selected cases,
and solver semantics.

Freeze the complete feature-correct argv and source/dependency hashes before
launch. One Cargo invocation only, including `--features
shadow-apply-candidate`; retain raw stdout/stderr, exact argv, status, wall/user/
system time, CPU, peak RSS, swaps and launch memory. No retry. A failed run
requires a fresh sprint before another Cargo attempt.

## Continuing proof lane — registered `lean_prover`

Write leases only:

- `notes/theory/lean/YulangClosure/FormalPermissionExportWitness.lean`
- `tasks/agent-loop/inbox/effect-permission-export-witness-proof.md`

Read-only dependencies: the exact checked 12 SourceOrigin and 11
ConstructorRealization theorem/type/transitive-axiom audit results on the hashes
above. Preserve their modules byte-for-byte. Define a decoder from the typed
constructor observations to the existing event-history relation, carrying
source owner, occurrence/path, original row and canonical representative
separately. Instantiate existing audited origin results from decoded records.
Do not assume `Origin`, `Construction`, canonical-image equality or exact export
as decoder premises when they are conclusions under study. State successful
native construction decoding, canonical transport, capture completion and
native export as explicit conditional gaps if not derived.

Maximum three serialized Lean/helper invocations sharing 180 seconds, one CPU,
1 GiB RSS per process. After a failure, another attempt requires a diagnosed
failure and changed proof source. Preserve all failed logs; no invocation after
three.

## Review, resources and stop conditions

After both lanes freeze, assign a fresh non-author read-only
`compiler_referee`. The reviewer must verify the exact final hashes, raw Cargo
receipt and all Lean audits, and test the four mutations listed above. Author
and reviewer cannot self-certify. Preserve the first unsatisfied transition and
do not infer universal source/native coverage from passing finite tests.

Total envelope: **1,500 seconds** — Rust 600, Lean 450, fresh review 250, Luna
100, dispatcher 50, contingency 50. At most two producers; zero Astra. At most
one heavyweight build/test process at a time. Cargo: one CPU, <=2 GiB RSS,
<=180 seconds, >=4 GiB available memory at launch. Lean: one CPU and <=1 GiB
RSS. Serialize heavy validation. This is a resource budget, not permission to
start more work if actual capacity is unavailable.

Stop on changed pins, another writer, unsupported correspondence, any
falsifier, invocation/resource budget exhaustion, or user STOP. Preserve all
unknown writers' reservations and quarantined paths. If either lane blocks,
continue only its independent in-envelope lane. Next related work under this
contract is limited to completing the typed joins and checking the frozen
decoder; any new source file, dependency, semantic choice or production path
returns to Luna first.

## Integration boundary

The whole language/native/production parent remains OPEN. Only Luna updates
`current.json`, adjudicates, stages explicit accepted research paths, commits
and pushes after full review of the exact outbound range. Keep incomplete Rust
instrumentation provisional. At sprint end update the compact state, freeze a
uniquely named outcome and consult the selector. No default/root theorem module
integration or production cutover is authorized here.
