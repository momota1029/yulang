Sprint R230 independent review — revision 1

Disposition: CLEAN within the explicit structural, allocated-query scope. No
blocking, major, or minor correctness finding identified.

Reviewer: `/root/r230_review`, independent compiler_referee, not a producer or
coauthor. The reviewer assessed the admitted contract, proof declarations,
governing design, and dependencies before reading producer explanations.
Baseline HEAD: `9137e14caa418cd3f686fc892b9cea9502a70b5f`.

## Reviewed result

The proof repairs R223's missing owner-local publication argument for R229's
actual successful upper-insertion histories, without replacing publication
with a full-store copy:

- Lines 90–201 derive bound-level closure, stopped closure, and SCC capture
  uniformity from successful upper-insertion histories.
- Lines 203–212 compute roots from the complete structural variable traversal
  and derive query coverage.
- Lines 284–453 recover owner reachability through SCC paths and existing
  `Published.copy` rules.
- Lines 478–559 establish forward and reverse publication transport;
  `mapped_normalized_base` targets R223's exact `normalizedBounds`.
- Lines 615–690 construct one diagonal valuation from an original constraint
  solution, preserving allocated inactive anchors and serving every requested
  use.
- Lines 705–737 instantiate actual self-upper and upper-only histories,
  retaining the external atom constraint in the latter.

Constructor coverage follows the inspected `vars`, substitution, and
`subst_equivalent` definitions: both kinds; all four Function ports with their
variance; record labels and optional flags; tuple order; variant payloads;
unions, intersections, and constants.

## Quantifier boundary

`terminal_solution_factorization` (lines 668–690) assumes:

```lean
problem.inputValid = true
UpperInsertionR229.History problem state
state.pending = []
problem.termAllocated query = true
problem.originalConstraints.Satisfied ρ
```

It does not assume a publication solution, stopped closure, SCC eligibility
uniformity, supplied root coverage, or a shared valuation. The original
solution is transported to physical bounds using R229's terminal permutation;
`publication_diagonal` constructs the publication solution.

Query allocation remains explicit. `inputValid` validates demand terms, not an
arbitrary separately supplied query (`AbstractSimpleSubCore.lean:80–92`). This
differs from query coverage, which is derived for arbitrary query terms. The
boundary matters: with scope size 1, `diagonal 1 ρ` maps coordinate 1 to
`ρ … 0`, so an unallocated query `.var 1` need not retain its original
interpretation `ρ … 1`. The result and handoff correctly preserve this
exclusion.

## Parent and native limits

The theorem applies to the original abstract constraint list under the stated
premises. It does not establish `SourceProblem.SourceScopedCoverage` or any
concrete `sameScoped` instance. The remaining bridge must, for every supported
source derivation at its original scope and the same witness, supply the
generated abstract problem, valid successful terminal history, allocated
query, original solution, and proof that the joint publication/use valuation
is `sameScoped` with that same witness. `PrincipalCoverage` additionally
retains its principal solution and `instanceOf` obligations (`Contracts.lean:
133–144`). Parent delta 0; roots 0/4; packages 0/5. No production promotion
follows.

Native exclusions match the inspected paths: capture uses current
representatives and metadata (`candidate_scheme.rs:1988–2012`); inactive owners
stop traversal (`:2400–2405`); roots include additional semantic interfaces
and evidence (`:2890–2967`); FreshUse resolves representatives again, combines
stored locality with live eligibility, and reuses the first representative
image (`:4581–4613`). These paths are not shown to realize R229 histories.
Representative changes, first-image eligibility coherence, extra effect
evidence, source witnesses, and inherited self-pair elision remain gaps.
`NO_SAFE_CODE_SLICE` is appropriate under this contract.

Relevant native tests were read, including shared FreshUse interface/anchor
checks and tuple reconstruction coverage; none were executed. This is static
review only: no Lean/Lake, builds, tests, or axiom checker were run by the
reviewer. The primary retains the separate kernel/type/axiom verification
obligation.

## Frozen inputs

| Artifact | SHA-256 |
| --- | --- |
| R230 contract | `38139890a715aa7c11a8a788d04ee442696c7755a38c7401988ad6201d3d5ef3` |
| R230 proof | `ee16a4e68bb6357a51877a83e78239db08a0789eecd090f387760db2c2632a50` |
| Proof handoff | `51cd2e92e40dd1a7545e539aa9adc30eae8fae3e2991efcebb69d550ad494848` |
| Owner handoff | `686d767736c3a813afbd0410fefdb1b9c6b60ea42b1deeaf60ab369a40cfb302` |
| R229 | `8f2132e050ea6a0de47eb7da3685d6116d8aedf64d59b02b399204d96735946a` |
| R223 | `65335f3b8c6834e1e1cd34429a8fd7330162648a62d532c3a45f44305b255aee` |
| Scoped publication | `d64e9bffca5d513985237a9ff78dcf3d9e43baae1594edbc93dff4b5410d428f` |
| Generalization | `3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246` |
| Abstract core | `023635d283f9a00e906ec965a6eaa5595eab21f2b93f353a1d5ea0ede0bffb6c` |
| Constraint syntax | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| Contracts | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| Native scheme | `6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e` |
| Native source | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| Top-level principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| Birth-level authority | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |
| Original source obligation | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |

Frozen target hashes were reauthenticated at review close. The changed
dependency cone contains no checker bypass or proof hole in the review scan.
The reviewer wrote no files, cache, scratch output, or Git state and started no
descendants. The explicit read-only instruction required the primary to record
this returned receipt.
