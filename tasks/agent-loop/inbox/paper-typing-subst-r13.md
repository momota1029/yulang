# R13 handoff — binder instantiation and substitution transport

Status: `SUCCESS_CHECKED_R13_SLICE`; full paper theorem remains `OPEN`.
Sprint contract `FULL-PAPER-TYPE-SUBSTITUTION-20261025/r13`, SHA-256
`0f8c6881ac95cebabf79de6fa4b81b514e78e41b5b5dc979bb8c2a3f34987c72`.
Baseline `396fe5335`; authority `docs/yulang-operational-type-safety-ja.tex:235-237,953-977`.
Primary `/root` was the only writer/checker; runtime exposes no UUID
(`UNKNOWN_CURRENT_SESSION_ID`). No child or reviewer was admitted. Eight
historical/foreign reservations stay quarantined. Writes stop after this frozen
handoff and state integration. Independent review remains `NOT_RUN`.

## Result and source correspondence

`instantiateType arguments body` now names the paper's leading type-binder
instance operation using `instantiateSubstitution`. The new general theorem
`instantiateType_subst` states, for any argument list whose length matches its
binder arity and any ambient `σ`,

```text
subst σ (instantiateType arguments body) =
  instantiateType (mapOperationArguments σ arguments)
    (subst (liftSubN arity σ) body)
```

Its proof composes `instantiateSubstitution_commutes` with `subst_comp`, making
the binder lift and ambient substitution order explicit.

Three paper rules are now represented and included in the six-family mutual
transport:

- `roll(v) : μ α.T` takes `v : T[μ α.T/α]`.
- `unroll(v)` takes `v : μ α.T` and returns `T[μ α.T/α]`.
- type application takes a value at `∀ α.T` and returns `T[A/α]`.

The canonical syntax nodes are `Ty.mu`, `Ty.poly`, `Value.roll`,
`Value.typeApplication`, and `Computation.unroll`. `PaperExecutionSyntax` now
imports `DeclSubst` for the shared instance operation and helper laws.

Exact concrete witnesses passed: `typeApplicationBoolVariable` applies Bool to
a context variable at `∀ α.α`; `rollVariable` and `unrollVariable` check the
fold/unfold directions for `μ α.α`. These are examples within the partial
judgment, not claims that type-abstraction introduction or all recursive types
are source-formed. Universal introduction/freshness and recursive graph
guards remain unrepresented. Other omitted paper rules, term substitution,
owner alpha-renaming, full paper typing, inference/executor and original A/B,
source/native, Rust, and review parents remain OPEN.

## Checked declarations and verification

`#check` printed exact types for `instantiateType_subst`,
`instantiateSubstitution_commutes`, the three typing constructors, three
concrete witnesses, `PaperValueTyped.subst_explicit`, and all five projections:
`ValuesTyped.typeTransport`, `ValuesAllTyped.typeTransport`,
`RecordPayloadsTyped.typeTransport`, `PaperContinuationTyped.typeTransport`,
and `PaperComputationTyped.typeTransport`.

Complete `#print axioms` results: `instantiateSubstitution_commutes`,
`instantiateType_subst`, every mutual/public transport, and the R10 operation
instance commutation dependency each report `[propext, Quot.sound]`. The three
concrete witnesses report no axioms. No `sorryAx`, `_f`, failed declaration
dependency, or project axiom appeared.

Pinned Lean 4.35.0; Lake `5.0.0-src+eb6cafb`; `-j1 -M1024`; serial execution.
R13 spent 7/8 serial Lean/Lake invocations and approximately 13.5 checker
seconds of 120:

1. Focused build — syntax module built; typing failed at normalization of the
   type-application, roll, and unroll result indices.
2. Focused build after adding normalized commutation equalities — failed because
   the mapped type-application/unroll syntax had not been exposed to the
   constructor goals.
3. Focused build after making mapped syntax explicit — exit 0.
4. Focused build after adding concrete examples — failed because the polymorphic
   variable typing needed an explicit indexed intermediate, and the unroll
   result needed reduction of `subst`.
5. Focused build with the intermediate judgments — failed because `subst` itself
   was not included in the example simplification set.
6. Focused build with the exact substitution reduction — exit 0.
7. `lake env lean -j1 -M1024 .lake/R13Audit.lean` — exit 0 (about 0.4 s).

The syntax dependency emits unused-binder linter warnings in existing mapping
proofs. They do not affect proof dependencies. `git diff --check` passed. No
tests, Rust build, default build, or production source changes were made. The
leased `R13InstantiationProbe.lean` scratch was not needed and was not created.

## Artifact hashes

- `PaperExecutionSyntax.lean`: `8789ee5a79b93d6fef2cff1db8692de67f4bc8b290a92ec3e37cac34b0074939`
- `PaperExecutionTypingSubstitution.lean`: `30f13a5fbbb11cd5763347efebcc5300e9119884eb4494a41d97bdaeb0731241`
- `PaperTypeSubstitution.lean` (read-only): `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a6eaa8e4861`
- `PaperTypeFormation.lean` (read-only): `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`
- `DeclSubst.lean` (read-only): `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`
- R12 handoff: `1f8932d19129d02cd6e170890078db81cc4c810e203bf593b582ebeef696790a`
