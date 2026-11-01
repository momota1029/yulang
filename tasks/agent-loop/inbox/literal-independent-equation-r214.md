# R214 literal equation — primary handoff (reviewed incomplete)

Parent: unchanged `Contracts.SourceProblem.InferenceSoundness`; same-assignment
solution-indexed soundness, no accepted-run premise.

Authority: adopted L1 source rule in
`notes/design/2026-11-02-literal-l1-adoption.md`. It fixes eight raw payloads,
`Value(τ(l))`, `v(l)`, pure `Return`, and original `(q,r,e₀,ξ,ω)`. It explicitly
does not define Simple-sub generation, satisfaction, readout or `sameScoped`.

Current mathematical target: establish the all-payload independent
Value/Effect generation and same-assignment readout equation, or stop at its
exact first missing equation. Preserve annotation synthesis versus
`writtenTarget`, checking alternatives, and enclosing effect obligations.

Relevant existing limits: `CanonicalSourceInferenceModelR196.literal_generated_formula`
is a source `Build` equation only; `LiteralAtom` consumes a supplied declaration
relation; regular graph satisfaction establishes `RegularSub`, not exact
descriptor identity; the current Simple-sub syntax carries no runtime literal
value field. A ground graph proposal needs explicit maps and a justified
source-independent payload provenance/readout.

Current status: model candidate frozen for fresh independent review; gate remains `MODEL-INCOMPLETE`; no theorem packet. Implementation lane:
`NO_SAFE_CODE_SLICE`. Review seam: independent falsification of all four
candidate equations against arbitrary assignments and the exact L1 coordinates.
Resources: 1,800 seconds model work, 600 seconds review; zero Lean/build/test/
Rust/Cargo/cache/scratch/worktree/new-environment activity.


Concrete falsifier recorded: a candidate with only `atom(τ(l)) ≤ var(q)`
accepts a graph assignment mapping `q` to `.top`, because the decoded pair
uses the lattice `top` rule and is `RegularSub` by `regular_fold`. This rejects that one-sided candidate,
not all possible equations. The exact first missing bridge is the source-independent literal
Value/Effect constraint equation and its relation to the descriptor/effect
coordinates in the same solution. The raw value can come from the literal
syntax; `sameScoped` must retain it alongside the assignment-derived
type/effect facts. `Sorts` and `LiteralDeclaration` remain abstract. No source
semantic choice is implied. Parent delta remains zero.


Frozen review boundary: the sole concrete countermodel rejects the
one-sided lower-bound candidate by assigning the literal's type variable to
`.top`. It is not a counterexample to every possible generator. Review should
confirm the exact lattice `top`-rule derivation and whether the localized
missing equation faithfully preserves L1 without assuming source typing. No
review receipt exists yet.


## Review disposition

Fresh independent review passed the frozen model hash
`9c19d9422b47408a6ee944d04b04ddb22d58047684144dfc276bfa6e5d01c6e9`. The
one-sided top-node countermodel is valid and correctly scoped; all 11 pins
match. No blocking, major or minor findings. Preservation is accepted only as
an explicitly incomplete research checkpoint. Full L1 equation, theorem
application, and parent delta remain open: **0/4 roots; 0/5 packages**.
