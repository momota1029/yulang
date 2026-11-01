# R213 — freeze the solution-indexed inference model

Status: **STOPPED_INCOMPLETE_REVIEWED**. R212 is frozen as `STOPPED_INCOMPLETE_REVIEWED` at
`7c25f1cce`; this sprint follows the user's adopted root-first research order.

## Original target and fixed scope

Keep the four unchanged roots in `notes/theory/lean/YulangClosure/Contracts.lean:128–154`:

```lean
InferenceSoundness:
  ∀ s x d a, supported s → generates s x d → solves d a →
    ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

The remaining roots are `SourceScopedCoverage`, `PrincipalCoverage` with its
original instance relation, and `InferenceTermination` for the actual
`inferInitial`/`inferStep`. Preserve every source constructor, scope, effect,
Call, and shared witness. Do not substitute native success or a successful
solver history for the independently supplied `d` and `a` of soundness.

The research order and model-freeze gate are fixed by
`notes/theory/2026-11-02-root-first-simple-sub-plan.md` (SHA-256
`890fa8a5a1c88c6400e293870598750b285fe12075ad13cbd3e884cc71921c16`). The
original algorithm authority is
`notes/design/2026-10-11-yulang-inference-top-level-principles.md` (SHA-256
`7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`). Literal
L1 is fixed by `notes/design/2026-11-02-literal-l1-adoption.md` (SHA-256
`f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8`); its
independent Simple-sub generation/readout is still to be established. The
typed-Union question remains pending only for dependent branch/result
telescope transport; structural Union remains in the core.

## Fixed outcome

Produce and independently review a constructor-by-constructor mathematical
model that separates:

1. original declarative source judgment;
2. independent generated type/effect constraints;
3. satisfaction of those constraints by one assignment;
4. reconstruction of the original judgment and `sameScoped` from that same
   assignment; and
5. the separate endogenous solver algorithm, its run/readout theorem,
   principality order, and termination relation.

For each equation, record its source owner and authority. Mark it either
`FIXED` by an existing decision/source or `OPEN` with the exact missing
equation and owner. No field may assume the source judgment, logical
admission, or readout conclusion that the original parent is meant to derive.
If any needed equation is `OPEN`, the outcome is `MODEL-INCOMPLETE`; do not
start a proof packet that assumes it. A complete document or wrapper is not
model completion by itself.

## Inputs and frozen pins

- `Contracts.lean`: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `OriginalSourceSyntax.lean`:
  `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`
- `OriginalSourceGeneration.lean`:
  `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`
- `OriginalSourceInterpretation.lean`:
  `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`
- `SimpleSubConstraintSyntax.lean`:
  `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6`
- selected Source-Generalize source schema: `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`
- Source-Generalize proof construction: `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`
- complete Call contribution: `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e`
- pure ReadInvoke result: `8d1eb7ecea3e63d7ba0ae091dc673f3321e52fc0e31c5d824bdf4f1656b99488`
- computed EvalInvoke/InvokeTail result: `2f3a5461b6dacaa29e881ba8b3003120b912e441dd5e4c47fc4ccaa27d3b31a6`
- annotation effect hygiene: `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`
- contextual residual lineage: `d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98`
- regular solution semantics: `755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29`
- regular graph store satisfaction: `c534c060dfde84f2817fbaa53222f430b59d9b6377cfacedabeca7b9b4b8ffa3`
- nonvacuous conditional singleton-formal App source fixture:
  `5e948a1f8a3aab66028f885ebf16b6ffeed81999039e8a5a4e9c3caf84464408`
- R212 frozen core: `023635d283f9a00e906ec965a6eaa5595eab21f2b93f353a1d5ea0ede0bffb6c`
- Root-first plan: `890fa8a5a1c88c6400e293870598750b285fe12075ad13cbd3e884cc71921c16`
- L1 adoption: `f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8`

Rehash all inputs before freeze. If a pin changed, stop and reconcile before
using its content. Do not read or alter pending question answers; retain the
typed-Union boundary above. The source map is documentary evidence only and
does not establish any of these equations as proved.

## Exact leases and lanes

Primary `/root` owns these new paths exclusively:

- `notes/theory/2026-11-02-fixed-inference-model-r213.md`
- `tasks/agent-loop/inbox/fixed-inference-model-r213.md`
- this sprint contract and `tasks/agent-loop/current.json`

One read-only `explorer`, `/root/r213_source_rule_map`, maps original source
constructors to source rules and authorities. It has no write/build/test/Git
rights. After the primary freezes the two deliverables, Luna assigns one fresh
read-only `compiler_referee` or `spec_auditor` to review equation fidelity,
independence, full source coverage, root composition, and the exact first open
premise. The author cannot self-review.

No proof worker is assigned in this sprint. A registered `lean_prover` may be
assigned only after the model review gate finds every equation needed by the
next proof packet fixed and authorized. If it finds an open equation, preserve
the exact owner and equation as the next source-model obligation.

## Resource limits and exclusions

- Primary model work: at most 1,800 seconds.
- Independent review: at most 600 seconds.
- Lean, Lake, builds, checkers, tests, Rust, Cargo, cache growth, new
  environment/worktree/target/scratch: **zero** in R213.
- No semantic changes, source-domain restrictions, Rust implementation,
  native correspondence claims, or pending-question edits.
- Keep counts at **0/4 roots; 0/5 packages** unless a reviewed theorem is
  applied to an unchanged original root.

## Acceptance and stop conditions

Acceptance requires a frozen model and handoff, exact authority for every
claimed fixed equation, all open equations named without hiding them behind a
`Kernel`/`LocalLaws` parameter, and fresh independent review. Any `OPEN`
equation yields `MODEL-INCOMPLETE`, no theorem worker, and zero parent delta.
Stop on changed source hashes, conflicting authorities, an equation requiring
a new semantic decision, or the resource cap. No unrelated paths are leased.


## Final review and disposition

The independent read-only compiler-referee review found one major omission: the
conditional `roleAndInitialCallOrigin` App atom. The primary added its exact
`singletonFormalCall` condition, same-witness coordinates, source fixture pin,
and independent-interpretation OPEN status. A fresh delta review passed the
repair and found no additional documentary correctness finding. All revised
artifact hashes and enumerated source pins matched.

The review accepts preservation of this explicitly incomplete checkpoint; it
does not pass the model-completion gate. Status remains `MODEL-INCOMPLETE`; no
theorem was admitted and no parent premise was discharged: **0/4 roots; 0/5
packages**. R213 used no Lean, Lake, builds, checkers, tests, Rust, Cargo, cache
growth, scratch, worktree, or question-board mutation. See
`tasks/agent-loop/history/20261102-fixed-inference-model-r213-outcome.md`.
