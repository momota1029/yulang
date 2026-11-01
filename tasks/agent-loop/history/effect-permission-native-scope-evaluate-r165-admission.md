# R165 admission — native scope evaluator refinement

Status: **ADMITTED**. User's ongoing Rust/Lean soundness goal supplies
continuation authority. Goal context: Yulang soundness (inference, executor,
effects, principality, termination), with explicit priority on effect hygiene.
No source-semantic change is approved by this packet.

- Branch and baseline: `yulang3`, `92b7b726e35476254b4772dc59a7881667e65916`.
- Contract: `tasks/agent-loop/sprints/effect-permission-native-scope-evaluate-r165.md`,
  revision 1, SHA-256 `6b40ab89d3956c4e7967a3c6a303fb4db9597e8f70df6103d4a7bfdee7e15062`.
- Governing policy: annotation effect hygiene SHA-256
  `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`;
  inference principles SHA-256
  `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`;
  compose scope construction
  `notes/theory/2026-10-15-compose-scoped-release-construction.md`.
- Exact source inputs match the contract before launch: `candidate_scope.rs`
  `4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03`,
  `candidate_context.rs`
  `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`, and
  `NativeScopeTransformer.lean`
  `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6`.
- Reused source boundary: R144 reviewed `candidate_scope.rs` test-only delta;
  R145/R147 keep source/native application and whole effect-hygiene gates open.
- Exact proof leases: `notes/theory/lean/YulangClosure/NativeScopeEvaluateRefinementR165.lean`
  and `tasks/agent-loop/inbox/effect-permission-evaluate-refinement-r165-proof.md`.
- Exact Luna source-handoff lease:
  `tasks/agent-loop/inbox/effect-permission-evaluate-refinement-r165-source.md`.
  Rust source/test files have read-only status; no Rust edit is admitted.
- Requested proof worker: registered `lean_prover`, `gpt-6-sol/high`, up to
  1800 seconds. Spawned as `/root/r165_native_scope_proof`; start receipt
  confirms all three dependency hashes and exact leases; effective model/effort
  are UNKNOWN. No separate runtime session ID was exposed. The worker was a
  leaf with only the exact proof leases above; it could not change source
  semantics, current state, or Git. Its final handoff records both artifacts
  frozen and writes stopped.
- Proof start receipt (runtime message):
  `/root/r165_native_scope_proof` acknowledged the R165 session, matched the
  contract and three dependency hashes, confirmed the exact two-path write
  lease, resolved pinned Lake/Lean 4.35.0 and began work. Requested routing is
  Sol/high; observed routing remains UNKNOWN. This receipt is transcribed here
  because the worker's result handoff is still in progress.
- Luna/source lane: bounded read-only inspection, up to 600 seconds. The primary
  owns only the source handoff and sprint records/current state.
- Fresh review allowance: up to 600 seconds total, no author self-review.
- Total sprint ceiling: 3000 seconds; Astra 0. Existing capacity override has
  already released 16 assignment slots; none are counted twice. Before launch,
  live roster showed `/root` and the completed dispatcher; no RUNNING/WAITING
  child needed notification. After launch, the proof worker is the only new
  child. The authenticated capacity receipt includes legacy identity `/root`
  and requires that historical worker row to remain UNKNOWN; the live primary's
  R165 source activity is separately represented in `active_sprint` and is not
  used to rewrite that released identity or recount its capacity.
- The R164 typed-Union question remains pending. R159 P/A, allocator/state
  authentication, actual Catch consumer, source/native closure, principality,
  termination and production remain OPEN.

## Proof completion and live-roster reconciliation

On 2026-11-02, the live collaboration roster was synchronized after the proof
handoff. `/root/r165_native_scope_proof` reported `completed`; the roster showed
that worker completed and all other listed children completed, with `/root` the
only running agent. The proof writer explicitly reported frozen artifacts and
stopped writes. Therefore its row is reconciled to STOPPED with the frozen
artifact hashes below; this does not change the separately authenticated
capacity override's historical `/root` UNKNOWN row or any path lease.

- Lean: `notes/theory/lean/YulangClosure/NativeScopeEvaluateRefinementR165.lean`,
  SHA-256 `5e3fa08db7403220f25b4a8ca2949dc8e7cdfc283b126622b77643880608ea55`.
- Proof handoff:
  `tasks/agent-loop/inbox/effect-permission-evaluate-refinement-r165-proof.md`,
  SHA-256 `b6a1045e9814bfce2a3ea58b9dfb4f4e760841806e3bb810adafa0ec823352ef`.
- State change: `active_sprint.proof.state=RESULT`; worker observation
  `STOPPED`; review remains pending. No lease is transferred by this receipt.

No dirty or quarantined path is leased, read, staged, or released by R165.

## Primary verification and independent-review start

Primary re-read the proof module and source handoff, recomputed all six artifact
hashes, and verified the three frozen direct source hashes. The primary reran
the focused pinned Lake module build and the bundled checker for all 15 public
theorems; both exited 0. The complete theorem types and axiom results are in
the frozen proof handoff. No Rust test/build was run.

Fresh read-only review started after synchronizing the live roster: the original
proof writer is completed, `/root/r165_lean_review` is RUNNING as the proof
reviewer, `/root/r165_source_review` is RUNNING as the source/compiler reviewer,
and `/root` is the primary. Both reviewers have exact frozen input hashes, 300
seconds each within the 600-second combined allowance, no write lease, and
explicitly cannot run checks, inspect unrelated dirty/quarantined paths, or use
Git. Their review-result or pending acknowledgement will be recorded after the
next live-roster synchronization.

## Independent reviews and adjudication

Both exact frozen outputs were independently reviewed within the 600-second
combined review allowance. `/root/r165_lean_review` found no blocking
mathematical issue: all 15 printed theorem types match, arbitrary unsorted and
duplicate initial lists are covered, and the reported transitive axioms are
within the project whitelist. It flagged the original Lean header as overstating
that Rust canonicality was discharged. Luna corrected only that header; the
reviewer confirmed the correction and the final artifact identity. Its final
Lean hash is `07f93963e223a1d8ad55b91fed94f4efe3e73459b94b96e1b7051b41a810bc2b`.

`/root/r165_source_review` found no blocking, major, or minor source/model
mismatch. It independently confirmed successful constructors, `then`, and
`remap` preserve the required ordered subinvariant; the Rust cursor and guard
branches match the Lean model; successful-return allocation boundaries are
accurately scoped; and caller state is empty in the inspected observation.
This is source inspection, not a formal Lean theorem for the Rust-to-Lean
encoding. It does not close source attribution, FreshUse authentication, actual
Catch use, or whole-language hygiene.

After the header correction, Luna reran the pinned focused Lake module build and
all 15 bundled theorem/axiom audits; both exited 0. The handoff now references
the final Lean hash and its final SHA-256 is
`8398752890ad0976f5f9d6f9725f62de5b7dbb2a4c53fa5760a32dcd2249a21b`. Remaining
formal premise: encode every successful Rust transformer into the Lean model,
prove its `Canonical` obligations and binary-search/membership correspondence,
and later authenticate the concrete source/native route and state.

Primary adjudication: ACCEPT the bounded evaluator refinement and the source
invariant inspection. This closes only R165's local cursor-to-denotation and
local representation-inspection gates. The larger effect-hygiene and soundness
goal remains active. Both reviewers stopped; no leases transferred. No Rust
source, tests, expected outputs, or quarantined paths changed.

## Sprint-end dispatch

The dispatcher proposed R166: encode successful native `ScopeTransformer`
representations into Lean, derive constructor/`then`/`remap` canonicality and
binary-search/membership correspondence, then apply R165. This can proceed
without answering the pending typed-Union question. No R166 lease or worker is
started by this recommendation; Luna will admit it under the continuing goal
with a new frozen baseline after this checkpoint.
