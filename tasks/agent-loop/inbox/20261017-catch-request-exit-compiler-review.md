# Catch Request-exit compiler review receipt

Verdict: CLEAN within the assigned bounded static source/native correspondence scope. No BLOCKING, major or minor finding. This is independent review of the frozen artifacts, not semantic adoption, proof closure or production certification.

Reviewer: `/root/catch_request_exit_compiler_review`; requested compiler_referee / Sol / medium. Effective runtime model, effort and session ID: UNKNOWN (no runtime receipt supplied). No authorship or edits of either target; the Luna source-instance artifact was reviewed as an untrusted target against the source owners, not as proof-construction evidence. Baseline/commit `a372e6163` supplied by Luna; Git inspection prohibited and omitted.

## Frozen bytes

- Contract revision 2: `fd45f91858c063665ab51ce0c581ad179dfbfc24a6d60e87d552a2c14a094781`.
- `notes/design/2026-10-17-catch-request-exit-introduction-proposal.md`: `b0881f12db88442cc0cdbc0f13c08671ec1f083e78f21898bca09575f0be700f`.
- `notes/theory/2026-10-17-catch-exit-source-runtime-instance.md`: `5b7177e3f185c6c777dd2b0794c1f30fe17815c7ac99ee03dbb1d5f82a91376f`.
- Proof handoff: `edce02b4c4736d5f59f59ba31071a5aa9cb7e31b526fc6834f9e4043982164e4`.
- Source-instance handoff: `3ee51d3ac4713ba7f73371bf8521a7a1b2ae5d070bea0489fc5c8c8b78833e7c`.

All above hashes independently matched current file bytes. All 16 direct contract dependency hashes and all five additional transitive pins listed in proposal section 8 independently matched. Hash verification is byte identity evidence only. Governing adoption scope, matcher interface, source-owner outside equation, typed-boundary receiving/incidence clauses, IF-Use limitation, and top-level inference principles were inspected directly; historical reviews and implementer explanations were not accepted as evidence.

## Independent source checks

`local_source.rs:1117–1184` retains actual syntax/scope and continuation ordinal 1. `candidate_source.rs:769–810` retains the original scrutinee endpoint/effect and arm-body occurrence; `:870–886` accumulates scrutinee/arm effects and arm values, including the separate no-value-arm normal-return edge. `candidate_effect.rs:864–928` uses one declaration environment, response polarity pairs, original scrutinee result endpoints, slots 62/63 and entry/full-S slots 64/65. None constructs a dynamic q, complete dependent response/future family or typed outside matcher use. `candidate_context.rs:3001` implements argument swap/result preservation under retained parent context; `:3201–3255` records conditional scoped observations and consumes relation/filter evidence, not Request-exit source typing.

`machine.rs:1582–1608` allocates one event and pending request with authentic execution observations and empty suffix; `receiving.rs:205–234` authenticates execution and records event-bound observations. `machine.rs:1235–1313` validates current installation, declaration, local grant when required, signature and payload before the binder response guard. The Function-response binder branch returns HandlerEvidence at 1303 before capture at 1305 and Catch pop at 1312. This confirms only conditional local playground noncoverage. Wildcard continuation skips that binder guard; earlier lowering/ownership/payload checks may fail first. No language-wide refusal follows.

`machine.rs:1013–1082` validates saved frames and publishes a template with the original declaration/event; `:1380–1413` unwinds actual owner/handler frames into the same pending request suffix. `continuation.rs:13–21` retains original_event as lineage. Selected H is not included by the selected capture/pop path; forwarded handler frames have their own explicit representation. `enter_template` uses existing runtime control remapping, which supplies no complete typed dependent action. The targets explicitly preserve this limit and do not claim an actual specimen execution.

The relevant `candidate_operation_catch.rs` test helper and cases were read, including the callback-response specimen, negative callback interfaces, unused packet fields and direct/aliased resumption effects. The helper checks structural recoveries but its lowering result does not establish absence of partial-HIR diagnostics. Thus the targets correctly refuse to infer complete source acceptance or dynamic execution from the conflict-free assertion.

## Cause and invariant assessment

Proposal section 3 identifies the first missing construction at the actual complete operand use at outside μ_H, under the stipulated original typed Request and actual exit. This is the responsible source typing/transition owner; downstream scalar endpoints, stored metadata, transport algebra or deletion of a runtime tag guard cannot repair that cause. The statement is conditional on the original δ/ε premises, not a claim that the concrete specimen supplies them.

Proposal section 4 agrees with the directly inspected source-owner section 6 and typed-boundary incidence equation: historical q/eligibility remain indexed at yield; consumed H has no current incidence at C_out; other candidates require their own current owners. No historical-to-current cast, state restoration, new Observe, assumed M_exit, narrowed response quantifier or typed Δ_q construction is claimed. Outside matching, mismatch/false guard, NoArm and suspended paths remain explicit obligations. The local runtime path performs compatibility checks while the delimiter is active; the targets do not equate that with general adopted outside selection.

Original FORWARD-FIRST-CALL A/B, full F1, separate FK1, CATCH-EXIT-INPUT-1/M_exit and every other parent OPEN status remain unchanged. No semantic adoption or production readiness is certified.

## Resources, omissions and STOP

Cap: 120 seconds; conservative charge: 120 seconds. Final review clock observed `2026-10-17 05:09:28 UTC`; exact launch timestamp and CPU/peak RAM were not instrumented. Checks were targeted static reads and SHA-256 verification only. Initial `python` hash command was unavailable; `python3` completed the byte checks. No Git, tests, builds, Cargo, probes, runtime execution, network, descendants or contacts other than the primary. Full parent-theorem proof and all-input native correspondence were outside this bounded review.

Only this authorized receipt path was written. STOP after receipt hashing; no background work or descendant/writer lease remains. Receipt hash is reported separately to avoid a self-hash cycle.
