# R215 outcome — shared source/solution readout candidate

Status: **STOPPED_INCOMPLETE_REVIEWED**. The model gate remains `MODEL-INCOMPLETE`; roots remain **0/4**, packages **0/5**. R215 creates no theorem and closes no premise of original `InferenceSoundness`.

## What changed in the mathematical picture

R214 rejected one-sided lower-bound/direct-node readout. R215 identified two-sided literal bounds as a stronger candidate: on the same regular graph, mutually related nodes are equivalent and the earlier `.top` model fails the reverse comparison. The independent reviewer verified the exact lattice clauses and equivalence lemmas. This is still not equality with the original source `Descriptor`, and no graph-to-source endpoint map is established.

For annotation hygiene, the original source carries only an annotation `Nat` ID. The source rule forwards that ID at the original Lambda/formal coordinates. The abstract Simple-sub store has comparisons but no annotation declaration, owner/path/event or endpoint-readout interpretation. Existing `LiteralDeclaration` is supplied separately to `OriginalSourceInterpretation.LiteralAtom`. R208's candidate `Solves` assumes the same environment/tree and coordinates rather than deriving them from the generated store; it does not prove the original Kernel atom.

The next missing construction is therefore a source-resolved declaration table and a source-independent type/effect denotation, tied by generation to the same assignment and scope. It must preserve composed polarity, permission/allowance, actual inflow, residual, symbolic row links, and the full original witness. Rust grammar/observer evidence is not a mathematical proof premise.

## Verification and review

Pinned Lean 4.35.0/Lake 5.0.0 build passed for `OriginalSourceGeneration`, `OriginalSourceInterpretation`, and `SimpleSubLatticeInference` (18 jobs), using the user-authorized cache at `notes/theory/lean/.lake/build`. This verifies those existing modules only. Independent review PASSed only for checkpoint preservation as incomplete; see `20261102-source-solution-readout-r215-review.md`. No theorem, axiom audit, Rust, Cargo, or test run occurred.

Frozen candidate: `notes/theory/2026-11-02-source-solution-readout-r215.md`, SHA-256 `c3044d07f4290b019e2a181b032e314501ddc1bc9e37e9d8725cec3898973866`. Next selection is constrained to build the original declaration/denotation equation or stop at its first exact missing owner equation. No new Rust observer slice is admitted.
