# R285 independent review — complete storage inventory and frozen frontier

Review-only gate after R285 producer STOP. Use the existing 900s Sol review
grant within the admitted 3,600s envelope; no producer renewal. Preserve the
unchanged R70 parent and all open source/native/production gates.

## Frozen target and authentication

Initially read/hash only this contract. Return actual reviewer identity and
hash, then WAIT for Luna's separate GO. Do not read the manifest or technical
inputs before GO.

After GO, the first technical operation hashes the explicit manifest
`tasks/agent-loop/sprints/extrusion-storage-closure-r285-review-inputs.json`,
SHA-256 `acce9085a3432ccdcf451cf72a7978fe810991830385bd85cb3a934c4eb6740b`, and all 32 exact repository-relative paths.
Render only MATCH/MISMATCH. Stop on a missing path or true byte mismatch.
Then inspect the model's actual consumers/mutators before reading the frozen
R285 module and handoff.

## Independent review questions

1. Is the State-field / Work-constructor inventory complete against the actual
   model consumer definitions? Check raw and canonical row references, kind,
   bounds, latent use, publication/transfer and every mutation owner.
2. Does `StorageClosed` match that complete inventory and imply R284
   `CaptureComplete`, exclude both reviewed counterexamples, and hold for all
   `Computed.rowInput caller` inputs as stated?
3. Resolve the boundary for `State.operation.caller` and saved Parent callers:
   are their row endpoints opaque external request payloads, or stored row
   references consumed by `boundRequest`/later model work that the invariant
   must validate under the contract's every-field inventory? The arbitrary
   `Request` initialization theorem is an exact constraint. Report any
   contract/construction conflict without silently narrowing either claim.
4. Independently inspect the exact open selected-Work goal through `perform`.
   Is it only a proof gap, or can it be completed/falsified with a concrete
   satisfying state? Do not call it a counterexample without a kernel-checked
   falsifier.
5. Independently audit the caller-row counterexample and its parametric
   no-universal theorem, exact quantifiers and use at the initialization
   boundary. Does it establish a source-reachable defect? It must not be
   promoted beyond the model claim.
6. Verify every one of the 19 theorem types and complete per-theorem axiom
   lists, including the reported `Classical.choice` use. Compare the full
   consumer table, all Work/result/failure cases, `select` pop and partial
   publication. Identify exact open obligations and the first owner.
7. Independently run focused Lake build, direct Lean check and the bundled
   checker for the frozen module under Lean 4.35.0 with the exclusive cache
   lease transferred after producer STOP. No broad build or tests.

## Scope and ownership

Fresh identity `/root/sol_r285_storage_closure_review`, registered
`lean_prover`, requested Sol/high, maximum 900s, no descendants. Exclusive
`notes/theory/lean/.lake/build` is transferred to the reviewer. All 32
manifest inputs, including R70 authority, R283/R284 evidence, R285 contract,
admission and outputs, remain immutable. No source/Rust/Cargo/probes/external
bodies, artifact writes, Git or semantic changes. Luna owns
`tasks/agent-loop/history/20261103-r285-independent-review.md`, adjudication,
current state and subsequent selector consultation.

The reviewer must distinguish a valid local model fact from R70, source/native
correspondence, accepted source reachability, Simple-sub A/B, Parent and
production closure. If a required contract decision remains ambiguous, return
the exact inconsistency and STOP; do not invent a domain change.
