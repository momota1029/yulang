# Sprint FULL-PAPER-TYPE-SUBSTITUTION-20261025/r16 — common strong-induction syntax mapping

Status: ADMITTED by Luna for bounded primary-led proof construction.
Branch `research/simple-sub-intrusion`; baseline `71e40c382e8caf2114d8d6819215ab0c8605a428` (frozen R15 result). Authority: `docs/yulang-operational-type-safety-ja.tex:203-207,237,953-977`; workflow: `rules/goal-driven-sprints.md` and the 2026-10-16 decision. Original user goal and all A/B quantifiers remain unchanged.

## Original outcome and success evidence

Prove the raw syntax mapping prerequisite to the paper's type-substitution/forall-introduction obligation, then apply it to the actual declaration table. For every `n : Nat`, `σ : Nat → Ty`, and raw syntax object `x`, establish:

```text
mapFamily (liftSubN n (liftSub σ))
  (mapFamily (liftSubN n shiftTypeSubstitution) x)
= mapFamily (liftSubN n shiftTypeSubstitution)
  (mapFamily (liftSubN n σ) x)
```

Cover all nine families and every constructor: `Value`, `Computation`, `PatternPlan`, `ConstructorBranch`, `GuardedBranch`, `ValueArm`, `OperationArm`, `HandlerPlan`, and `MapperPlan`. Then derive the corresponding `TemplateBody`, `OperationDeclaration`, `NominalConstructor`, `PrimitiveSignature`, and `DeclarationTable` commutation, including actual executable template code. No code, guard, default, arm, operation instance, attached list, option, product, type application, or declaration entry may be omitted.

### Fixed proof construction

Define a proof-only `ShiftAt n : Prop` structure with nine fields. Each field states the displayed law for objects of one family whose `sizeOf` equals `n`. Prove `∀ n, ShiftAt n` by one `Nat.strong_induction_on`; do not use `Value.rec`, mutual `induction`, or adjust their motive order. For each field, use ordinary `cases x`. Every recursive child is discharged only by the common strong IH at `sizeOf child`, with a strict inequality derived from the actual constructor and list membership/projection facts. For attached lists, optional guards/defaults, and nested products, map the elementwise IH into the exact mapped container. Under `Value.typeAbstraction`, increment ambient depth. Under `OperationArm`, use its actual `rigidBinders`; the child depth is ambient depth plus that binder count. Keep depth generalized in every field, so all nine family IHs are available at each child depth.

Project the nine fields to named public lemmas. Reuse them for template code and each declaration-entry map, then prove `mapDeclarationTable_shift_substitution_commutes` for operations, nominal constructors, primitives, templates, and the unchanged native-list identity. Use `liftSubN_add` and explicit arithmetic normalization only where required by nested binders.

Do not alter `PaperExecutionSyntax.lean`, typing judgments, source meaning, quantifiers, or add the forall-introduction rule. Do not assume a mapping law, identify code mapping with identity, use `sorry`/`admit`, add project axioms, narrow the paper domain, or bypass the checker.

## Parent, premises, and source path

Parent: full paper typing substitution, including the value-only forall-introduction rule and the original full inference/executor and A/B obligations. R15 proved no new parent premise. The exact remaining prerequisite is the nine-family law above, followed by template/declaration mapping. Even success here does not prove the forall rule, six-judgment reindexing/transport, full typing, recursive graph guards, inference/executor, original A/B, or source/native/Rust correspondence; all remain separately OPEN.

Source path for this packet is the actual mutually recursive syntax and `mapPaper*` definitions in `PaperExecutionSyntax.lean:38-500`, plus declaration maps at `:491-542`, and their consumers in the paper typing judgments at `:617-716`. No source-to-constraint-to-native conclusion is claimed by a mapping lemma. Implementation lane: `NO_SAFE_CODE_SLICE` for this proof-only packet. The two inspected Lean owners are `PaperExecutionSyntax.lean:38-542` (the raw syntax/mappers and declaration map) and `PaperExecutionTypingSubstitution.lean` (judgment substitution theorem); modifying either would widen the exact lease or change the semantics/judgments that this prerequisite must preserve. No Rust or production path is approved here.

## Inputs and exact ownership

- Baseline R15 handoff `tasks/agent-loop/inbox/paper-typing-subst-r15.md`, SHA-256 `40d45d0b5755f032876a9cbfdd9a70c0e547b6aa8abb64747c0ba990fae061a7`.
- Candidate `PaperExecutionBinderLaws.lean`, SHA-256 `59a4dd5cd4a8056196f3e0d084869099f78039d083b7b47d7e9a1d3e6c0296a0`.
- Syntax `PaperExecutionSyntax.lean`, SHA-256 `8789ee5a79b93d6fef2cff1db8692de67f4bc8b290a92ec3e37cac34b0074939`.
- Typing `PaperExecutionTypingSubstitution.lean`, SHA-256 `30f13a5fbbb11cd5763347efebcc5300e9119884eb4494a41d97bdaeb0731241`.
- Type substitution `PaperTypeSubstitution.lean`, SHA-256 `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861`.
- Type formation / `liftSubN`, `PaperTypeFormation.lean`, SHA-256 `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`.
- Declaration substitution `DeclSubst.lean`, SHA-256 `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`.
- R13 hash erratum is preserved in R15 receipts; corrected `PaperTypeSubstitution.lean` hash is the one above. R14's 13/12 and R15's 12/12 call charges remain frozen and do not transfer.

Proof owner `lean_prover`: one continuing packet covering the fixed stages above, with no authority to change scope, budget or dependencies. Exact writer leases: `notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean`, `notes/theory/lean/.lake/R16Audit.lean`, and `tasks/agent-loop/inbox/paper-typing-subst-r16.md`. Luna owns this contract and `tasks/agent-loop/current.json`. All listed dependencies are read-only. No other writer, reviewer, Astra, Rust lane, or production source is admitted in this packet. Eight existing historical/foreign UNKNOWN reservations remain quarantined.

## Resources, checks, and stop conditions

Maximum 1800 active seconds, 12 serial Lean/Lake invocations, and 180 checker seconds. First construction call must instantiate the exact common `Nat.strong_induction_on` structure and at least one nontrivial syntax case; no recursor/motive reconnaissance. At most 10 construction calls and reserve two calls for final focused build, exact theorem types, and complete axiom audits. One Lake process at a time; Lean commands use `-j1 -M1024`. No tests, default-target build, Rust build, or parallel checker.

Stop at the first unproved strict decrease, a constructor/container mapping mismatch, a depth or binder-count equation that cannot be justified, any omitted code/guard/default/arm/declaration case, the call/time ceiling, or an unsafe lease/dependency change. Preserve exact diagnostics in the handoff. If blocked, freeze the actual partial artifact and describe a changed next method; do not spend outside this packet.

## Acceptance, review, and next boundary

Success requires a focused successful module build; exact types and complete axiom audits for all nine laws, `TemplateBody`, every declaration entry, and `mapDeclarationTable_shift_substitution_commutes`; all constructors/containers/decreases accounted for; no `sorryAx`, `_f`, failed declaration dependency, or project axiom. A clean helper-only build is not success. Freeze coherent bytes for fresh independent review by an eligible reviewer; Luna adjudicates before any parent gate is promoted. Review checks all nine constructors, actual `sizeOf` evidence, nested binder depths, declaration code and the parent application. Independent review is currently NOT_RUN and no reviewer is admitted by this contract.

Only after this mapping prerequisite passes should Luna consult the dispatcher for the next parent-application packet. On a concrete obstacle, return the exact constructor/equation and Lean diagnostic. No beyond-contract production, semantic, source/native or Rust change is proposed.
