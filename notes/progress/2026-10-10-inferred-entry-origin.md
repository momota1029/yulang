# Inferred-entry source origin record

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Status: inert source-origin evidence retained; authorization and circuit
certification remain open

## Authority and scope

This implements the inferred-entry evidence requirement in the
[contextual attachment/admission design](../design/2026-10-10-contextual-attachment-admission-design.md)
§§4–7, specifically its Function-port and rollback contracts. The
[cycle-certificate gap map](2026-10-10-context-cycle-certificate-gap-map.md)
identified `admit_lambda_fact` as the source owner. The change adds no new
semantics and authorizes no context operation.

## Retained source fact

At `admit_lambda_fact`, when the candidate graph creates the fresh inferred
entry and return Effect rows and admits the slot-3 entry-to-return constraint,
it retains an `InferredEntryOrigin` containing:

- the source Lambda occurrence;
- the fresh entry and return Effect-row endpoints;
- the exact slot-3 constraint occurrence and cause.

The record is distinct from `EntryCertificateId`. Written annotation
construction does not create one. No producer can yet consume it to mint
`BothFromRight`; the operation remains unconstructible in production and
freshening continues to reject certificate-bearing contexts.

The origin vector is included in retained-capacity accounting and the existing
context checkpoint/rollback path. A failed route truncates the record; a
supported retry retains one record with the restored sequence position.

## Evidence and limits

Independent semantic and spec reviews passed the frozen three-file delta.
Focused checks passed:

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test --offline -p yu-solver --features shadow-apply-candidate --lib inferred_entry_origin -- --test-threads=1` (2 passed).
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test --offline -p yu-solver --features shadow-apply-candidate --lib value_entry_first_edge_failure_rolls_back_and_retries -- --test-threads=1` (1 passed).
- Scoped `git diff --check` on the three changed paths.

This proves only that the source owner retains the exact inferred-entry
construction fact and that the existing route transaction restores it. It does
not establish inferred-entry authorization for function-port propagation,
complete SCC/circuit recognition, reverse dependencies, invalidation or
withdrawal, private deferral, publication, or certificate-dependent rollback.
Both approved unbounded circuit classes, complete Call, full effect hygiene,
soundness/principality, ordinary/default inference, and F5 replacement remain
open.

The configured CLI fallback was tried once in the current API session. Its
event stream showed no dispatch to the registered `prover` child, so this turn
does not count that attempt as prover use. Earlier verified prover outputs are
recorded separately; the current collaboration schema still omits that role.
