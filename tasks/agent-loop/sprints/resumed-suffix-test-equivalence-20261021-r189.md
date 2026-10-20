# Sprint R189 — resumed suffix source equivalence

Status: ACTIVE, primary-only source comparison; no code or semantic authority.
Branch: `research/simple-sub-intrusion`; baseline `183d69ef36cf45753980a83b7eecefd303421650`.
Authority: continue the unchanged computation-forwarding preservation parent and preserve all R187 claims, source domain, outputs, and OPEN gates. R188 is ended; its unused time does not carry over. No subagents; Luna is the only worker.

## Outcome

Determine whether the unchanged positive test
`runtime_unmatched::unmatched_request_preserves_original_suffix_across_outer_handling`
and the negative guard
`runtime_resume::fresh_owner_reentry_does_not_resurrect_an_expired_receivers_grant`
are source-equivalent for request handling modulo binder renaming and primitive
values. Trace only source distinctions that can affect owner, current event,
authenticated observations, receiver boundary, annotation family, ordered
handler selection, and continuation capture. Success is either a source-grounded
distinction that justifies their opposite outcomes or a precise test-contract
conflict with the original semantic decision still unresolved.

## Inputs and exact leases

Read pins at entry:

- `tools/inference-playground/src/runtime/receiving.rs` — `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9`
- `tools/inference-playground/src/runtime/machine.rs` — `7187abd78ca13efaeebf4cb70837c98360c0024d082a59af331da41169d3409b`
- `tools/inference-playground/tests/runtime_unmatched.rs` — `480229b78a1203c5c23fc4d7de78f9c7c257a1d8024661c3a24f9cd3fbbf1208`
- `tools/inference-playground/tests/runtime_resume.rs` — `ec87db17fa228b90332a2b4c71bbafed2e70f6aad6c6c26d441edd7aea4e6426`
- R188 frozen result — `36607b78325c9b7b1012a20014119d3b3647eb4e976e40ca8dd79214cabfb961`
- R187 primary readback — `1f39ea63031edc2325ab7013518f0c7e34fb275b134ebf6b47ba546013b988ae`

Write only this contract, `tasks/agent-loop/inbox/20261021-r189-source-equivalence.md`,
and primary-owned `tasks/agent-loop/current.json`. No compiler/test edits or
expected-output changes. Do not modify R187/R188 frozen artifacts.

## Method and boundary

Compare the two fixture strings modulo binder renaming and integer literals;
check whether any remaining source distinction changes the relevant runtime
premises above. R188's temporary alias candidate made both event-1 handlers
eligible and therefore violated the negative test. Do not revive it or infer a
semantic rule from that experiment alone. No tests are needed for this source
comparison. If no relevant distinction exists, report the conflicting expected
outcomes and leave implementation, semantic approval, parent theorem, A/B,
source/native correspondence, and production gates OPEN.

Maximum active work: 300 seconds; no carryover. Fresh independent review is
unavailable under the solo-worker constraint. Preserve all unrelated dirty and
untracked paths.
