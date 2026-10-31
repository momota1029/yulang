# Sprint EFFECT-PERMISSION-SYMBOLIC-PUBLICATION/20261102-R126

Status: ADMITTED bounded Rust-to-existing-R39 publication-transition audit. The standing Rust/Lean soundness and effect-hygiene goal remains open.

## Parent, objective and claim boundary

Parent: Yulang soundness/effect hygiene; conditional R125 same-graph PRE projection. Preserve the original parent claim and quantifiers. Determine for one actual `FormalEntry` invocation whether the real symbolic drain preserves the retained permission Vec (`V1 = V0`) and whether retained direct requests project to the exact two publication slots (45 then 46), preserving typed endpoint identity, order and multiplicity. Apply only existing R39 declarations. If either equation fails, give the first actual owner and source-qualified counterexample.

Trace the actual call path and every mutation footprint reachable before publication. Separate canonical fact deduplication from append-only provenance multiplicity. Reconstruct each direct request from its retained FactId/provenance edge to the original retained term; the facts Vec alone is not accepted as a trace. Keep external inflow and later consumer correspondence outside this packet.

No new model, theorem, axiom, assumed simulation law, source change, test, build, Lean execution, checker, storage probe, environment/cache/worktree/copy, or dirty/quarantined read. Static source reads use `git show` at the exact pins only. R111's 6 GiB private verification-resource gate remains unchanged and blocks Rust integration.

## Frozen inputs and leases

Baseline branch `yulang3`, commit `e4570173a19ed72f6257fa391032f153ca43943d` (exact source blob hashes are recorded in the manifest). The R39 theory blob remains pinned to commit `1f5835c276143537ec58ed81db96c7c108cea8e7`. R125 source, proof and reviewed outcome are frozen direct dependencies.

- Rust source lane owns only `tasks/agent-loop/inbox/effect-permission-symbolic-publication-r126-source.md`.
- Registered `lean_prover` owns only `tasks/agent-loop/inbox/effect-permission-symbolic-publication-r126-proof.md`; it applies authenticated equations to existing R39 and reports theorem names/types/premises without adding declarations or running Lean.
- Luna owns this contract, manifest, admission, current state, review, outcome and Git.

Inspect `candidate_effect.rs`, `lib.rs`, `candidate_context.rs`, `candidate_intrusion.rs`, `candidate_extrusion.rs`, `candidate_scope.rs` and `term.rs` only as reached by the actual call path. A newly reached unpinned owner stops that branch and returns the exact dependency request; do not expand the manifest autonomously.

## Required evidence and falsifiers

Report the ordered call path from effect admission through typed drain, context/replay and publication; list every relevant write and show a frame argument for the permission Vec. Establish whether any successful path mutates it. For retained direct requests, trace original term identity, endpoint fields, ordered provenance and multiplicity through FactId lookup and the two slot projections. Account for generated effects, substitutions, suppression and successful/failed helper outcomes as actual control-flow cases. Distinguish an unavailable source fact from an empty projection.

Falsifiers are an actual successful helper path that changes the mapped permission Vec, or a direct request whose source identity, endpoint, slot, order or multiplicity changes before publication. Do not use arbitrary malformed states as source counterexamples. Do not equate a conditional R39 application with full parent closure.

## Resources, review and stop

Caps: source 600s, proof 300s, fresh independent compiler referee 180s after both handoffs freeze; primary integration 300s; total at most 1,380s; Astra 0. No builds/tests/checker/Lean execution/storage probes; source edits false. Each assignment gets one frozen handoff file. The reviewer independently inspects the pinned sources before reading producer explanations, checks equations/call path/control-flow boundaries and verifies handoff hashes. STOP at the first unpinned dependency, unclear retained-term identity, or envelope boundary.

Rust integration stays **NO_SAFE_CODE_SLICE** unless a separately admitted verification-resource and source-lease gate changes. R126 can establish useful source correspondence but does not authorize code edits or production promotion.
