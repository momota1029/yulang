# R304 independent review

Frozen Lean artifact: `SourceEffectRetentionR304.lean`, SHA-256
`b2f070b78c9b347db6cb3710e542a1d03db596a4a64af3915985f2bc41ff0706`.
Producer handoff: `source-effect-retention-r304.md`, SHA-256
`1b155daeabe808f30a183037f609e4a7cf0b1a4c2ed7a336053902a86c2a93bf`.

Independent Lean review passed a fresh isolated Lean 4.35.0 build and printed
the types and complete transitive axioms of all six declarations. Each uses
exactly `[propext, Quot.sound]`; all 12 dependency hashes were unchanged. The
independent audit log SHA-256 is
`af7f926fa3902f00b6da3a8f46dfe72cf4a1f8ecafedbdf84bbd7bcb50e96ff3`.
The construction derives copy inputs and readback under the stated operation,
capacity, run and idle hypotheses; the two supplied tail values are independent.

An independent parent-edge audit found no defect in the bounded statements.
The actual Rust fixture is not encoded as these inputs, and signed extrusion
and same-route FreshUse tail readback remain unproved. The run starts after the
initial construction; it does not establish original publication or resume the
external extrusion machine. No theorem is applied to R293, R302 or R159: the
parent-edge discharge is zero. Original checking, event/world coherence and
independent admission remain open. The producer handoff records the exact
missing source equations and printed theorem types.
