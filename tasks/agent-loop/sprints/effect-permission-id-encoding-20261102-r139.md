# R139 — derive stable identity codes from a snapshot table

Status: admitted, source and abstract-proof lanes in parallel.
Goal: source/native identity correspondence for formal permissions; original
`SourceProblem.InferenceSoundness` and effect-hygiene H remain OPEN.
Baseline: `4c1d58a646a1101c080659ebfed6ae7862d8aded` (= `origin/yulang3`).
Inputs: R137 outcome `82fd775010eb1b865928510bed1d34d282c0d46768f6ee93054ca0d670748231`; R138 outcome `080b15b31f4231611143279e6604f88285dd0ce29940fd28fd8f728e06bacd64`.

## Outcome

Assess a snapshot-local, append-only table whose tagged keys retain cloned Rust
identity values and use their complete `Eq`. Establish the exact key expressions
for source owner, HIR occurrence, formal, annotation scope, source node/effect
declaration and any required symbol, then use the **same table** for source
annotation and native retained metadata. Repeated concrete members must reuse
their code without changing sequence order or multiplicity. Codes from separate
snapshots are never compared. A failed reservation/lookup cannot yield an
authenticated partial snapshot, and the encoder remains test-only/read-only,
unconnected to solver admission.

The source handoff should provide a complete in-memory Rust candidate/patch,
including exact Eq evidence, type/variant tags, source-field equations,
byte/hash target, and failure boundary; do not modify Rust source in this sprint.
The Lean lane proves table-only properties constructively: equal keys resolve
to the same code, distinct registered tagged keys remain distinguishable,
append preserves prior codes, and failed construction yields no authenticated
snapshot. No injectivity axiom or native-output-equality assumption. Rust `Eq`
correspondence remains a separate source premise.

## Assignments

**Source:** Luna/high implementer, 900 seconds, exact output only
`tasks/agent-loop/inbox/effect-permission-id-encoding-r139-source.md`.
Read immutable committed blobs at baseline, especially `crates/yu-hir/src/module.rs`,
`source_annotation.rs`, `crates/yu-syntax/src/full_parse.rs`, `candidate_effect.rs`,
`candidate_source.rs`, and only necessary session/batch owners. Do not inspect
dirty diffs or quarantined/untracked work. No Rust source writes, build/tests,
Lean, Git mutation, scratch, or solver integration.

**Proof:** registered `lean_prover`, 600 seconds, exact outputs
`notes/theory/lean/YulangClosure/FormalPermissionIdentityEncodingR139.lean`
and `tasks/agent-loop/inbox/effect-permission-id-encoding-r139-proof.md`.
Construct the finite tagged-key table and prove the stated properties from its
definition. Report theorem types and complete transitive `#print axioms`.
Existing pinned Lean only; at most one direct check, 120 seconds, 1 CPU, 1 GiB.

Fresh independent review: one reviewer, 240 seconds, exact receipt
`tasks/agent-loop/history/effect-permission-id-encoding-20261102-r139-review.md`.

## Falsifiers and limits

Stop if artifact/parse identity can collide under ordinal/offset alone, tags
confuse variants, source and native metadata use different tables, cloning
changes equality/code, append reassigns earlier codes, or failure leaks a
partial authenticated snapshot. Keep native inventory equality, internal
consumers, A/B, H and production OPEN. Total envelope 2,100 seconds; Astra,
Cargo, new environments: zero. Only Luna owns state and Git.
