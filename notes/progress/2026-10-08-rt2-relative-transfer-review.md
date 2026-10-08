# RT.2 relative-transfer research review

Date: 2026-10-08
Review mode: focused compiler-referee review of one conditional evidence pair
Result: no finding within the frozen research claims
Production inference gate: remains open

## Frozen artifacts and review scope

The reviewer inspected these exact frozen artifacts:

- [Finite separation and legal-model boundary](../theory/2026-10-08-rt2-relative-transfer-countermodel.md), SHA-256
  `52f67a5608895008a6b7cf69094e8b6badf8b51f9234a1f2eead73780c19ddbf`.
- [Constructive proof attempt and precise obstruction](../theory/2026-10-08-rt2-relative-transfer-proof-attempt.md), SHA-256
  `8158ebaccc43fc92297c4fe8a12a6dad10e21429cb279a7fe25b292b9577ecff`.

The review tested mathematical/semantic soundness of the finite monotone
counterexample, the conditional source-shaped realization, the non-hole RT.2
gap, and the status of the proposed enlarged apply-hole coalgebra. Governing
inputs were outer-introduction §3 (RT.2), input-realization §3.2 and the
selected captured-closure constructor definition §3.

## Result

No finding applies to the frozen conditional claims.

The positive map in the finite system is monotone. Its greatest fixed point is
all false; adding the declared holes at `a` and `s` gives
`beta=(true,true,true,false)`. Thus the non-hole source readout holds while the
target readout fails, despite ordinary final-model inclusion. This establishes
the stated algebraic separation only.

The source-shaped realization correctly remains conditional on authentic
full-domain witnesses and global `VIncl(G,C)`. It does not infer global
emptiness from one examined provider or a reduced universe. The constructive
attempt correctly distinguishes relative `A_f` membership from the absent
relative `A_f -> F_c` observation action. The enlarged step coalgebra remains
a proposal: postfixedness and independent hole-replacement fronts are unmet
premises, not proved consequences.

## Scope not reviewed or established

The review does not establish a complete legal Yulang countermodel, uniform
relative transfer, RT.1/RT.3, complete coalgebra postfixedness, a foreign
embedding, production conformance, or F5 cutover. It closes no theorem or
production gate.

No edits, Git operations, tests or builds were part of the review. The
reviewer's report was the sole independent certification; the producer's
derivation and the primary's reread were not counted as review.
