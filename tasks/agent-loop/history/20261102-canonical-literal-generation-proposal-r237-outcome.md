# R237 outcome — literal generation proposal

Prepared and independently reviewed a source-indexed, gate-ready proposal
connecting the adopted L1 literal row to a possible Simple-sub generator and
writing the exact literal obligation for the unchanged
`SourceProblem.InferenceSoundness` root (`Contracts.lean:128–130`).
Final reviewed proposal SHA-256:
`d5162f2cf08eda28455d0a086205811c12c26d2bf99dff92712ef87934bb3eab`.

The proposal keeps fixed source facts separate from candidate generation and
the still-open arbitrary-assignment bridge. L1 fixes all eight payload/type/
value rows, empty intrinsic effect, pure Return and original
`(q,r,e₀,ξ,ω)`. R236 supplies a checked payload map, canonical type/value
equations, coordinate preservation and the exact unannotated R196 symbolic
`Build` consumer. Neither establishes generation authority or arbitrary
solution readout.

Fresh `spec_auditor` review passed proposal accuracy and found an authority
blocker: L1 expressly withholds a generator clause; top-level principles permit
source construction but do not select all-eight direct generation; the pinned
Simple-sub branch supports direct canonical generation for Int only. Adopting
the proposed bounded all-eight equation therefore requires a scoped user
decision unless an exact authoritative source already establishes it. No
semantic adoption or theorem activation occurred.

Parent-premise delta: **0**; closed roots: **0/4**. Remaining after any adoption:
independent constraint semantics; derivation from every satisfying assignment
to the original endpoint's descriptor, value, root and event; intrinsic effect
and pure Return in the full assignment model; and same-scope/shared-witness
application inside the original parent. Call/effects, checking alternatives,
principality, termination and Rust correspondence remain separate.

Implementation remains `NO_SAFE_CODE_SLICE`: neither the candidate source
producer nor runtime literal decoder supplies this arbitrary-assignment
theorem. No test names or expected outputs changed. R237 used no cache,
environment, worktree, Lean/build, Rust/Cargo or tests. Unrelated dirty files
and UNKNOWN/quarantined paths were preserved.
