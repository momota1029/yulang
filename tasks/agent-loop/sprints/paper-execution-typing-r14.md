# Sprint FULL-PAPER-TYPE-SUBSTITUTION-20261025/r14 — universal introduction

Status: primary-owned continuation of the user's fixed inference/executor
proof goal. Branch `research/simple-sub-intrusion`; admission baseline
`06fc932be71b3125f7455ef4ef0f08ace6b100e1`. Authority:
`docs/yulang-operational-type-safety-ja.tex:203-207,237,953-977`.
R13 is frozen at `tasks/agent-loop/inbox/paper-typing-subst-r13.md`, SHA-256
`bf91e3df9bbaa30b7ea8bc92eb33d406fcf775851c3aec87e7d13730780bff94`; its
input-hash correction is
`tasks/agent-loop/inbox/paper-typing-subst-r13-erratum.md`.

## Fixed outcome

Represent the paper's value-only universal introduction rule with its freshness
condition encoded by extending the type-variable scope: shift declarations,
graph types, and the entire shared term environment together under the binder.
The body must be typed at the polymorphic body type in those shifted contexts;
the conclusion is `typeAbstraction body : .poly bodyType` in the original
contexts. Keep the paper's value-only restriction and do not add this rule for
computations or continuations.

Connect the rule to R13's type application and preserve all existing R13
constructors. Generalize the mutual type-substitution transport over declaration
and graph environments so the recursive type-abstraction premise is transported
under `liftSub σ`. Prove, from the actual mappings, the required commutation
between shifting an ambient environment and applying a lifted arbitrary
simultaneous substitution. Do not hide freshness or mapping laws in `LocalLaws`
or new assumptions. If the existing fixed-index judgment cannot represent this
scope extension soundly within this packet, record the first exact Lean
obstruction and stop before weakening the source rule.

## Exact ownership and dependencies

Primary `/root` owns:

- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`
- new `notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean`
- `notes/theory/lean/.lake/R14Audit.lean`
- this contract, `tasks/agent-loop/current.json`, and the R14 handoff
  `tasks/agent-loop/inbox/paper-typing-subst-r14.md`
- primary Lean/Lake cache

Read-only: `PaperTypeSubstitution.lean`, `PaperTypeFormation.lean`,
`DeclSubst.lean`, the cited paper, and the frozen R13/R13-erratum records.
Eight historical/foreign UNKNOWN reservations stay quarantined. No child or
reviewer is admitted. Rust/native and production files remain outside this
proof slice (`NO_SAFE_CODE_SLICE`).

Input hashes at admission:

- `PaperExecutionSyntax.lean`: `8789ee5a79b93d6fef2cff1db8692de67f4bc8b290a92ec3e37cac34b0074939`
- `PaperExecutionTypingSubstitution.lean`: `30f13a5fbbb11cd5763347efebcc5300e9119884eb4494a41d97bdaeb0731241`
- `PaperTypeSubstitution.lean`: `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861`
- `PaperTypeFormation.lean`: `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`
- `DeclSubst.lean`: `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`

## Resources, checks, and stop conditions

Maximum 1800 active seconds, 12 serial Lean/Lake invocations, and 180 checker
seconds; `-j1 -M1024`, one checker at a time. R13 charges do not transfer. Build
the focused modules and run exact-type/complete-axiom audits for the new
freshness/commutation lemmas, type-abstraction constructor, existing six-family
transport, and R13 application witnesses. Run the required sprint static
consistency check at the boundary. No tests, Rust build, default-target build,
or production edit.

Stop on an exact scope-index/capture counterexample, an unsound freshness
encoding, a concrete mapping-commutation obstruction, loss of an existing
typing witness/rule, any need to narrow the paper source domain, unsafe lease or
dependency change, user STOP, or budget limit. Preserve failed diagnostics.
Never add `sorry`, `admit`, project axioms, checker bypasses, hidden context
assumptions, or a computation-level universal introduction rule.

## Acceptance and remaining boundary

Success requires the focused build, a checked value-only type-abstraction rule
whose premise shifts declarations/graph/shared Γ together, checked arbitrary-σ
transport of the full represented mutual slice including that rule, exact types
and full axiom audits, and the positive R13 Bool type-application witness still
passing. Record the exact source-to-constructor mapping and all omitted forms.

This remains a partial extrinsic judgment. Full paper rule coverage, recursive
graph formation/guards, term substitution, owner alpha-renaming, complete paper
typing, inference/executor, the original A/B obligations, source/native and Rust
bridges, and independent review remain OPEN.
