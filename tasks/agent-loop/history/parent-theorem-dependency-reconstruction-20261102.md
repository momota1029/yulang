# Parent-theorem dependency reconstruction — 2026-11-02

Status: **research plan and dependency audit**, not a proof, semantic adoption,
or closure receipt. The user redirected the active work away from repeated
owner-local investigations and asked for dependencies to be rebuilt backward
from the original theorem statements.

## Original Lean obligations

The authenticated `YulangClosure.SourceProblem` in
`notes/theory/lean/YulangClosure/Contracts.lean:103–154` is an abstract record.
Its declarations are proposition definitions and independent fields, not a
concrete instance of Yulang inference or proofs of those propositions.

- `InferenceSoundness` (`:128–130`):
  `∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a`.
  This is the forward theorem. Every satisfying assignment is quantified, and
  the same assignment `a` must appear in the shared scoped conclusion.
- `SourceScopedCoverage` (`:133–135`):
  `∀ s x e d, supported s → sourceJudgment s x e → generates s x d →
  ∃ a, solves d a ∧ sameScoped s x e a`.
  This is the reverse existence direction. Forward soundness does not imply it.
- `PrincipalCoverage` (`:138–144`) additionally takes `principal` and
  `instanceOf` relations as parameters. It requires a principal solution and,
  for every original source derivation, a solving assignment related by
  `sameScoped` and the original instance ordering. Neither relation is
  selected merely by proving soundness or finite-source coverage.
- `InferenceTermination` (`:152–154`) is accessibility of the actual
  `inferStep` relation from each supported initial state. It is algorithm
  termination, not termination of the user's source program.
- `NativeCorrespondence` (`:147–149`) is a later bridge from native success to
  generated/solved constraints. It cannot prove the mathematical solver's
  soundness. `Elaboration` (`:123–125`) is separate as well.

## Backward dependency graph

```text
original source judgment and shared scope witness
                 ▲
                 │ original source rule induction / readback
complete source Build/J_m satisfaction under one assignment
                 ▲
                 │ missing: derive from actual generator + solved constraints
actual Simple-sub generation C and independent denotation σ ⊨ C
                 ▲
                 │ concrete type/effect constraint calculus and generator
accepted source syntax and Simple-sub algorithm

source derivation ── actual generated C ── satisfying σ ── shared witness
        │                       └──── SourceScopedCoverage
        └── principal relation / universal factorization ── PrincipalCoverage

actual inference states and every transition ── well-founded measure
                                            └── InferenceTermination

proved mathematical algorithm ── later source/native/Rust simulation
```

The key missing shared edge is: actual constraint generation plus the
independently defined type/effect satisfaction relation yields the *complete*
original source derivation under the same assignment, telescope and witness.
The original source materials distinguish declarative typing, construction of
`Build`, and global satisfaction of its clauses. Satisfaction of `Build` is
not the denotation of solver constraints by definition. Existing
reconstruction results can be consumed only after their full source-side
hypotheses are supplied; they do not themselves establish the generator to
solver bridge.

For source coverage, trace an original derivation into the **same actual
generated constraint object** and construct a satisfying assignment that
preserves its shared scope. A separately chosen schema, native model, or
independent witness does not count. Principality then adds the original
ordering and a universal factorization of every source derivation through one
principal solution.

Termination needs a separate measure over the actual inference transition
relation. Structural finiteness of source syntax does not bound propagation,
fresh extrusion copies, SCC-qualified intrusion, equality repropagation,
generalization, or retained suspension continuations.

## Evidence and boundaries

The inspected original source documents give separate meanings to source
judgment, constructor-directed generation, and one-assignment scoped clause
satisfaction. They provide useful mathematical construction results relative
to stated local laws, but the current `SourceProblem` declarations do not
instantiate those fields with the actual Simple-sub constraint calculus.
`generated_application_checking` consumes full source-side satisfaction and
extracts an already admitted candidate; it is not an inference-success-to-
admission constructor. This bounded evidence does not prove that no concrete
instance or theorem exists elsewhere.

Call and contextual effects belong in the abstract soundness theorem wherever
the accepted source rules and Simple-sub algorithm use them. They cannot be
delayed if doing so narrows the original theorem. Rust details, native
success/simulation, and runtime behavior come after the mathematical theorem.

The governing success metric is the set of named premises in these original
propositions that are actually discharged or refuted. A conditional helper,
reviewed proposal, local lemma, test count, or theorem count is not progress at
the parent unless its premises are independently established and its
conclusion removes a listed edge.

## Revised research sequence

1. **Abstract Simple-sub soundness:** define the original constraint grammar,
   independent type/effect denotation, source-directed generation and source
   judgment; prove the same-assignment soundness theorem for the complete
   accepted source domain, including Call/effects where they occur. Apply it
   to `InferenceSoundness`. Do not assume source admission, define solving as
   source typing, or hide obligations in unproved `LocalLaws`.
2. **Principality and termination:** prove `PrincipalCoverage` with the
   original ordering and universal factorization, and prove `InferenceTermination`
   by a separate well-founded argument over all transitions. Coverage remains
   a separate premise and may be proved independently once one canonical
   generator/denotation is fixed.
3. **Remaining source features:** prove additional Call/contextual-effect
   lemmas only where they are not already part of the abstract core theorem.
   Existing reviewed hygiene results are reused with their exact hypotheses.
4. **Implementation correspondence:** only after the mathematical model is
   fixed, prove the Rust solver realizes its generation, propagation,
   generalization and solving relations. Keep `NativeCorrespondence` and
   implementation correctness distinct from the source theorem.

The next bounded proof packet is R184: construct the canonical abstract
constraint/generation model and attempt the full forward theorem. Coverage,
principality and termination remain separate gates. If the accepted sources
leave an equation semantically open, stop and present that exact choice rather
than resolving it inside a proof packet.

## Authenticated sources

- `notes/theory/lean/YulangClosure/Contracts.lean`, SHA-256
  `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md`, SHA-256
  `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`
- `rules/compiler-engineering.md`, SHA-256
  `4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9`
- Original source definition/proof and source-safety paper, pinned in R184's
  contract.
- R183 stop/replan receipt, SHA-256
  `3178e92e4d6565fca58a9ea20c4bff7aac613cc2fa409600ce35a8f982304f50`.
