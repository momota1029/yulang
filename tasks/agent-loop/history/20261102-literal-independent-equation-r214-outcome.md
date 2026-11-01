# R214 outcome — adopted L1 literal equation

Status: **STOPPED_INCOMPLETE_REVIEWED**. The exploratory checkpoint is accepted
for preservation; model gate remains **MODEL-INCOMPLETE**.

## Parent accounting

The unchanged original roots remain open: `InferenceSoundness`,
`SourceScopedCoverage`, `PrincipalCoverage` with the original factorization, and
`InferenceTermination`. R214 closed **0/4 roots** and **0/5 packages**. It did
not define a full L1 equation, admit a theorem, or discharge an original parent
premise.

## Evidence and result

The frozen research note is
`notes/theory/2026-11-02-literal-independent-equation-r214.md`, SHA-256
`9c19d9422b47408a6ee944d04b04ddb22d58047684144dfc276bfa6e5d01c6e9`, pushed as
research-only commit `1016496ab`.

Its concrete result is a countermodel to one candidate only: a literal type
atom constrained by a one-sided lower bound `atom τ(l) ≤ var q`, with readout
that interprets `q` as the assigned upper graph node. Mapping `q` to `.top`
satisfies the actual lattice `RegularSub` relation and the singleton store,
while direct node readout is not the exact intrinsic base descriptor. The
candidate is refuted; stronger/two-way constraints and source subsumption are
not refuted.

The raw literal value can be constructed from source syntax. The remaining
L1 obligation is the independent Value/Effect store equation and its
same-assignment relation to the original descriptor/effect coordinates,
including any source rule needed when the solution is a supertype. Preserve
`(q,r,e₀,ξ,ω)`, annotation synthesis versus `writtenTarget`, and the full
contextual permission/inflow/residual distinction. Existing source `Build`
reconstruction and `LiteralAtom` do not supply this bridge.

## Independent review

Fresh read-only review PASSed with no blocking, major or minor findings. It
verified the top-node derivation, the limited claim scope, the syntax-derived
payload distinction, and all 11 pinned evidence hashes. It accepted only an
explicitly incomplete research checkpoint. See
`tasks/agent-loop/history/20261102-literal-independent-equation-r214-review.md`.
No Lean/build/test/checker/Rust/Cargo/cache/scratch activity occurred.
