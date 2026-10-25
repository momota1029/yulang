# Sprint FULL-PAPER-TYPE-SUBSTITUTION-20261025/r15 — raw syntax mapping commute

Status: primary-owned continuation of the user's fixed Lean inference/executor
proof goal. Branch `research/simple-sub-intrusion`; admission baseline
`98ce61f57`. R14 is frozen at
`tasks/agent-loop/inbox/paper-typing-subst-r14.md`, SHA-256
`97af38cac56251166ea14e2ef87a02d33ffbdeae2dcd61fdf21319d8af375063`.
R14's 13/12 call overrun remains fully charged to R14. Authority:
`docs/yulang-operational-type-safety-ja.tex:203-207,237,953-977`.

## Fixed outcome

Prove the binder-depth-generalized raw syntax mapping commutation needed by
R14, using `sizeOf` strong induction and the actual constructors/mappings. The
equation for a syntax object `x` at any ambient binder depth `n` is:

```text
mapSyntax (liftSubN n (liftSub σ))
  (mapSyntax (liftSubN n shift) x)
= mapSyntax (liftSubN n shift)
  (mapSyntax (liftSubN n σ) x)
```

Cover all nine mutually recursive syntax families: `Value`, `Computation`,
`PatternPlan`, `ConstructorBranch`, `GuardedBranch`, `ValueArm`,
`OperationArm`, `HandlerPlan`, and `MapperPlan`. Cover every constructor,
attached list, optional guard/default, tuple/product, type application,
operation instance, template use, and rigid operation-arm binder count.
Handle nested type abstraction by increasing the depth; derive every strict
size decrease for recursive children from the actual constructor and list
membership facts.

Use the resulting computation theorem for `TemplateBody`, then prove
commutation for operation, nominal, primitive, and template declaration
entries and assemble `mapDeclarationTable_shift_substitution_commutes`.
Do not edit syntax or typing judgments or add the forall-introduction rule in
this packet. Do not exclude executable code from declarations, identify code
mapping with identity, or assume any mapping law.

## Exact ownership and dependencies

Primary `/root` owns only:

- `notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean`
- `notes/theory/lean/.lake/R15Audit.lean`
- this contract, `tasks/agent-loop/current.json`, and
  `tasks/agent-loop/inbox/paper-typing-subst-r15.md`
- primary Lean/Lake cache

Read-only: R13 `PaperExecutionSyntax.lean` and
`PaperExecutionTypingSubstitution.lean`, `PaperTypeSubstitution.lean`,
`PaperTypeFormation.lean`, `DeclSubst.lean`, the cited paper, and frozen R14
handoff. No child, reviewer, Astra, Rust lane, or production source is admitted.
The eight historical/foreign UNKNOWN reservations stay quarantined.

Input hashes:

- candidate `PaperExecutionBinderLaws.lean`:
  `59a4dd5cd4a8056196f3e0d084869099f78039d083b7b47d7e9a1d3e6c0296a0`
- R13 syntax:
  `8789ee5a79b93d6fef2cff1db8692de67f4bc8b290a92ec3e37cac34b0074939`
- R13 typing:
  `30f13a5fbbb11cd5763347efebcc5300e9119884eb4494a41d97bdaeb0731241`
- R13 hash erratum:
  `6a7fa2b2257012a81a669361a468789dedf4de27ce4fb07eaf5f3cac8ec4a09b`

## Resources, checks, and stop conditions

Maximum 1800 active seconds, 12 serial Lean/Lake invocations, and 180 checker
seconds; `-j1 -M1024`, one checker at a time. R14's 13/12 invocations remain
charged there and do not transfer. Reserve at most 10 calls for construction
and two for final focused build/type/complete-axiom audit. First build the
current candidate helper; if it fails, preserve that failure and repair it
before extending the module. Run the sprint static consistency check at the
boundary. No tests, default-target build, or Rust build.

Stop on a constructor with no strict `sizeOf` decrease, an unresolved binder
depth equation, any omitted nested code/guard/default/arm case, a need to assume
the mapping law, an unsafe lease/dependency change, user STOP, or the call/time
limit. Preserve exact failures. No `sorry`, `admit`, project axiom, checker
bypass, or narrowing of the paper source domain.

## Acceptance and remaining boundary

Success requires a focused successful module build; exact theorem types and
complete axiom audits for the nine-family syntax commutation, `TemplateBody`,
all declaration-entry maps, and `mapDeclarationTable_shift_substitution_commutes`;
all constructors and strict decreases accounted for; no `sorryAx`, `_f`, failed
declaration dependency, or project axiom. Until this passes, the candidate
helper is not checked and R14's environment results remain only local
elaboration evidence.

This proves only a mapping prerequisite. The value-only forall-introduction
rule, six-judgment reindexing/transport, full paper typing, recursive graph
guards, inference/executor and original A/B obligations, source/native and Rust
bridges, and independent review remain OPEN.
