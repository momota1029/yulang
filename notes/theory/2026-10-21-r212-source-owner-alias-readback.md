# R212 — Effect(10) owner representative and captured-bound inventory

The corrected targeted test passed once. Captured stdout SHA-256: `55d0e38b4648456c6b0b4bbfb55197a5526dac05fa215fab72175312e540f8a9`; stderr SHA-256: `1f97b3d3e80b42218786e48198dc4a535de6065b00d050cc494b2a1f967b9efe`.

The exact local provider is binding `relay`, called by Apply occurrence 18; its source callee occurrence is 19 and route 1. Lambda occurrence 12 slot 4 is completed source relation 71, with task Effect(10) ≤ Effect(31), admission 64, and physical emission 61 at Effect(10)'s upper-row lane index 0.

`candidate_intrusion::State::rep` returned Effect(10) for Effect(10) and Effect(31) for Effect(31). The route Capture map sends local Effect(31) to fresh Effect(32). The complete effect-bound list in this route Capture is:

| Relation | Captured source bound | Captured graph rows |
|---:|---|---|
| 72 | Effect(31) positive ≤ Effect(28) positive | 31 positive → 28 positive |
| 73 | Effect(31) positive ≤ Bottom positive | upper endpoint 31 negative in signed graph |
| 56 | Effect(23) negative ≤ Effect(12) negative | 23 positive → 12 negative |
| 57 | Effect(12) negative ≤ Effect(23) negative | 12 positive → 23 negative |
| 62 | Effect(12) negative ≤ Effect(29) negative | 12 positive → 29 negative |
| 53 | Effect(29) negative ≤ Effect(9) negative | 29 positive → 9 negative |

No captured row or bound uses Effect(10), and none connects Effect(10) to Effect(32). The source slot-4 bound relation 71 is absent from the route's Capture fibers. The actual route's Replay dependency for source relation 95 (child 96; lower 92, upper 95) retains the ordered Value inputs at ValueRow(18); it does not add the missing effect edge to the Capture graph.

R187's source-constructor analysis identifies the lower effect as relay's body Apply effect `q_u` and the upper as its Lambda return `r_u`, both allocated at local level 2, with Capture boundary 1. R212 directly confirms their emitted slot-4 relation, exact physical owner, exact local relay binding, and FreshUse result image. The source edge is local and source-generated, yet its owner is outside the Capture frontier.

## Result

This is a source-qualified candidate counterexample to the claim that the candidate local Capture/FreshUse constructor preserves every actual source Name/Lambda edge through its frontier. It realizes the mixed-cutoff pattern in an actual accepted local-source fixture, rather than only the abstract three-row skeleton. It does not refute the original native forwarding-preservation theorem or authorize a production change: the candidate's native correspondence and the complete original parent quantifiers remain open, and this result still needs fresh independent review/adjudication.
