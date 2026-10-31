# R79 — checked HIR definition to collected definition bridge

Status: admitted after R78 integration was rejected for an unbridged `DefId` / `DefinitionOrderId` type boundary. R78 artifacts remain frozen and unchanged.

## Fixed outcome

Construct a private, batch-owned lookup from an exact HIR `DefId` to the corresponding `DefinitionOrderId`, using only records already retained by `ConstraintBatch`: collected definition/root pairs, parallel HIR positions, and the owning HIR binding/root records. The lookup must validate batch ownership, HIR ownership, exact binding/root correspondence, ordinal/record agreement, and uniqueness. Keep the nominal identity types distinct: no casts, spelling comparison, local-ordinal equality, name-based fallback, or cross-type `PartialEq`.

Apply the checked result to both the R77 Name/DefinitionUse target join and R78 retained alignment consumers. Keep Name/use and Apply/checking occurrence coordinates separate. Preserve all calls and existing failure behavior; duplicate or foreign matches fail closed. Do not add persistent spelling-bearing collection storage or a new HIR field. If the retained ordered inventories cannot establish the bridge, stop and report the precise missing owner instead of expanding collection state.

## Exact assignments

- Rust implementation: `crates/yu-solver/src/lib.rs`, `crates/yu-solver/src/candidate_receiver.rs`, and `tasks/agent-loop/inbox/effect-permission-definition-bridge-r79-rust.md`.
- Constructive proof: `notes/theory/lean/YulangClosure/CollectedDefinitionBridgeR79.lean` and `tasks/agent-loop/inbox/effect-permission-definition-bridge-r79-proof.md`.
- Independent review after both author lanes stop: `tasks/agent-loop/inbox/effect-permission-definition-bridge-r79-review.md`.
- Luna primary only: central state, admissions, audit authorizations, adjudication, closeout and exact-path Git integration.

Rust and Lean work may proceed in parallel. The reviewer starts only after both writers freeze. Workers do not write central state or each other's paths. No HIR writer lease is granted.

## Proof and falsifiers

Lean keeps distinct `HirDef` and `CollectedDef` types. It constructs the bridge from ordered definition/root/HIR-binding records and proves: lookup agreement with the collection-time map; exact root and owner-coordinate preservation; uniqueness; foreign artifact/root rejection; and rejection of duplicate matches. Apply the bridge to R78's target comparison, without assuming equality of the distinct identity types.

Falsifiers include equal local ordinals from different batches, foreign roots/artifacts, wrong HIR positions, duplicate matching definitions, and a correctly named but distinct definition. Every unrelated competing call remains represented.

## Resources and boundary

Fresh envelope: 4800 seconds (Rust 1000; proof 1800; independent review 1000; primary 1000 including 500 closeout; Astra 0). At most two direct Lean stdin audits, each at most 120 seconds, require a separate exact-input primary authorization committed and pushed before invocation. No third invocation.

Same checkout only. No Rust compiler, Cargo, tests, builds, formatter, Lake, cache, target, scratch, new environment, or worktree. Preserve all 32 pending questions, UNKNOWN worker observations, and quarantined paths. Keep current state at or below 16 KiB.

Passing this packet closes only the typed identity-bridge checkpoint. Rust compilation/runtime, authenticated Rust-to-Lean extraction, genuine R66 Root, original A/B, soundness, principality, termination and production remain OPEN.
