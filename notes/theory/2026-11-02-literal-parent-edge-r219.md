# R219 — literal parent-edge construction

Status: in progress. Parent premise delta is 0 until a constructive theorem is
reviewed and applied to the original `InferenceSoundness` induction edge.

## Parent target and current cut

The unchanged root is `YulangClosure.SourceProblem.InferenceSoundness`:

```lean
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

The literal-specific target is to derive the adopted source introduction from
independent constraints and the same satisfying assignment. Source syntax
supplies the raw literal payload/value. The assignment must supply exactly the
adopted base descriptor and empty intrinsic effect at the original coordinates,
while retaining the original root, event, scope, occurrence, and shared witness.

R214 rejected a one-sided lower-bound/read-upper-node candidate with a `.top`
countermodel. R215's two-sided candidate uses regular-subtype equivalence and
therefore avoids that particular model, but it did not identify the same graph
assignment's equivalence class with the original `Descriptor`, map endpoints,
or supply the effect/readout equation. Neither checkpoint closes a parent
premise.

## Work and evidence

No R219 theorem or source correspondence finding has been admitted yet. The
exact frozen R214/R215 sources and their hashes are pinned in the R219 sprint
contract. Preserve the original L1 source rule from
`notes/design/2026-11-02-literal-l1-adoption.md`; no source semantics, supported
domain, or checking alternative may change.

## Accounting

At admission: roots 0/4; packages 0/5; parent delta 0; effect-hygiene theorem
delta 0. The acceptance gate is a reviewed constructive implication applied
to the original literal induction premise. A local definition or model lemma
alone leaves all counts unchanged.
