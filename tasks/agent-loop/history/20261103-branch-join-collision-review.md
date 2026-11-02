# BranchJoin collision: independent review

`/root/collision_lean_review` independently accepted the syntax-only result.
The module `notes/theory/lean/YulangClosure/BranchJoinCollisionR288.lean` has
SHA-256 `04b2fc7468bcad4e569a4bc0a9b8fa77a8fe9c603beeeac9c4fad5fc8ebe2870`;
the proof handoff has SHA-256
`3cbae12b7931e0865a404e9760ea31b7a8101e8764bb50ff8876e6001baa83c3`.
All eleven frozen inputs matched. Independent Lean 4.35.0 / `eb6cafb` checking
in a separate project and cache passed the nine named theorems. Their full
types and axiom lists appear in the handoff. `distinct_arm_kind` and
`distinct_sources` use `propext`; the other seven use `propext`,
`Classical.choice`, and `Quot.sound`. No proof holes, project axioms or kernel
bypasses were found in the inspected dependency cone.

The two raw Catch sources generate the same projected branchJoin Atom while
having different arm kinds and different complete generated rule trees. No
universal decoder from that Atom alone can recover their arm kind. They are two
sources; no impossibility is established for one authenticated source graph,
`Kernel.atom` with its environment, external lookup or complete child trees.
The examples have no independently supplied typing or operation-table
admission; no runtime or source-semantic failure follows. R159 is unchanged,
its admission and formation premises remain open and parent delta is zero.

`/root/branch_join_collision_review` separately accepted the bounded
source-realization stop report `branch-join-realization-r288.md`, SHA-256
`4d8b365f9ad8fe50f065a851d5d90da9b4c5c3510c3442af9f1dcd75df4326df`.
Its checker evidence concerns four existing declarations and supplies no new
source catalogue or parent premise. The new collision module is not an
independent review of those source-supplier obligations.

Both reviewers stopped without repository writes. No new language semantics,
source/native correspondence or production readiness is claimed.
