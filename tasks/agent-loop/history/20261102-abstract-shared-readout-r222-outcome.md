# R222 outcome — direct guarded readout blocked

R222's source/equation obstruction is independently reviewed. The reviewed
claim is limited to the direct encoding from the literal Fig. 12 equation into
the pinned guarded lattice graph. It does not refute a readout, store model, or
parent theorem.

## Frozen evidence

- Contract: `tasks/agent-loop/sprints/abstract-shared-readout-r222.md`,
  SHA-256 `d493b155e00c67e472aa88aaed62068bb412dcd071b4e87acb51743b2454e73d`
- Equation artifact: `notes/theory/2026-11-02-abstract-shared-readout-r222.md`,
  SHA-256 `8435d2610df65be3e547eaedeff8796228dec78628143b1ffe95d982b58e143a`
- Author handoff: `tasks/agent-loop/inbox/abstract-shared-readout-r222-proof.md`,
  SHA-256 `d5567ebcb53312d7a8280a855db41136b6422f78fa277334d2a6b664edcc192c`
- Read-only independent review, transcribed by Luna:
  `tasks/agent-loop/inbox/abstract-shared-readout-r222-review.md`,
  SHA-256 `50365f2c23498acaad58b3409b416bece545d9dd2a3990090f4fed66a397c1d4`

## Adjudicated result

The one-row `var 0 <: var 0` CoreProblem passes the actual `inputValid` and
`initial.insertPendingUpper` definitions, which leave a retained reflexive
constraint and an upper-bound self occurrence. Fig. 12's negative syntax is
`μn.n`; the explicit Top-seeded fold presents its body as `Top ∩ n`. The direct
body-root graph is `intersection(Top,self)`. It is Valid and fails the pinned
`Graph.Guarded`, because `FiniteLattice` requires both meet children to have
finite derivations. The equation artifact and the review both distinguish this
direct-encoding obstruction from inconsistency or semantic impossibility.

R222's success gate is unmet: no compiler, graph/reference/store theorem,
`ExactFig12Interpretation`, or axiom audit exists. No Lean build or cache write
was performed. The obstruction is **BLOCKING for R222 completion**, pending a
solution-preserving treatment of variable-bound cycles.

## Parent metric and next boundary

Original roots remain **0/4** and packages **0/5**. Parent delta is **0**.
The R212 endogenous shared-readout dependency remains open. No Rust/runtime
change is authorized or included; Rust remains `NO_SAFE_CODE_SLICE` for this
obligation. R221's literal source-carrier obstruction remains unchanged.

The next packet investigates finite quotienting of variable-to-variable bound
cycles while retaining free type parameters and universal substitution
factorization. It must not replace free variables with Top, change recursive
type semantics, assume a successful full solver run, or count store
satisfiability alone as principality.
