# R31 — native callback grant correspondence

## Objective

Advance the active `research/simple-sub-intrusion` objective by producing a
reviewed Rust correspondence patch proposal and a checked, source-directed Lean
bridge for the R26 callback-hygiene model. This is one finite-coordinate
projection step. It does not close the original source-preservation A/B claims,
whole-language hygiene, soundness, principality, termination, or production.

## Storage and execution boundary

Use only the existing checkout. Read the pinned R30 recovered-overlay archive
as a stream; do not extract a project or create a worktree, checkout, target,
cache, or helper build. Do not run Cargo or Lake. For Lean, use the pinned
`leanprover/lean4:v4.35.0` executable with the standalone source on stdin, capture
the theorem checks and full axiom audits, and verify that the invocation writes
no files. Preserve all unrelated dirty files and all UNKNOWN/quarantined paths.
In particular, do not edit the root runtime files or solver paths.

## Work packets and exact outputs

- Rust lane `/root/effect_permission_r31_rust` owns only
  `tasks/agent-loop/artifacts/native-callback-grant-r31.patch` and
  `tasks/agent-loop/inbox/effect-permission-native-callback-grant-r31-rust.md`.
  Map constructor fields to typed identities, request-owned observations,
  invocation guards, and selected dynamic Catch installation. Preserve
  `SourceOperationId` structurally as its source-effect family plus declaration
  `SourceNodeKey`; the family also carries its module and declaration key.
  `SourceNodeKey` equality uses parse identity, green-node allocation identity,
  and source start. Never use a Debug-rendered string as identity. R29 observed
  a Debug-string collision but did not test typed equality, so do not claim a
  typed collision or manufacture inequality. A proven typed collision for
  distinct operations, absent source field, or non-faithful mapping is a stop condition.
  Produce a proposed diff only; do not edit source files.
- Proof lane `/root/effect_permission_r31_lean` owns only
  `notes/theory/lean/YulangClosure/NativeCallbackGrantBridgeR31.lean` and
  `tasks/agent-loop/inbox/effect-permission-native-callback-grant-r31-proof.md`.
  Embed the exact pinned R26 model and define the native finite-coordinate
  projection. The R26 model uses numeric families and source sites, so define a
  finite encoding of the structural native identity pair and prove its
  round-trip/injectivity obligation; do not silently collapse identity to a
  spelling, Debug string, or source-site coordinate. State every remaining
  native extraction premise explicitly. Check every declaration and print
  complete axioms for every claimed theorem. A definition, unchecked
  declaration, or theorem assuming its conclusion is not a proof.
- After both outputs are frozen, independent reviewer
  `/root/effect_permission_r31_review` owns only
  `tasks/agent-loop/inbox/effect-permission-native-callback-grant-r31-review.md`.
  Review source correspondence, identity collision and round-trip obligations,
  theorem types, complete axioms, applicability, and claim limits.
- Luna primary owns the contract, manifest, admission receipt, stage ledger,
  current-state synchronization, adjudication, exact staging, and Git.

## Gates and falsifiers

The proof must derive the R26 predicates from the mapped finite coordinates and
faithful source premises. Falsifiers include a typed identity collision, failed
round trip, missing native premise, unsupported source/native correspondence, or
a theorem whose assumptions entail its conclusion. On any such result, record
the counterexample and keep all parent and production claims open. The reviewer
must be independent and must inspect the frozen inputs and complete Lean audit.

## Resources

Fresh 6,000 seconds: Rust 1,600; Lean 1,600; review 1,200; Luna primary 1,600
(including 500 seconds reserved for closeout); Astra 0. No R30 budget transfers.
Charge all packet work to this envelope. The selector's storage-light admission
simulation is selection advice only; actual state size and checker output govern.

## Completion condition

Complete this sprint only after exact inputs, patch proposal, Lean source and
complete audit, independent review, stage ledger, and closeout are recorded.
Otherwise close it incomplete with the exact blocker. This sprint cannot close
the original A/B obligation or authorize production semantics changes.
