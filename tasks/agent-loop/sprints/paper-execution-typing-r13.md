# Sprint FULL-PAPER-TYPE-SUBSTITUTION-20261025/r13 — binder instance transport

Status: primary-owned active continuation of the user's fixed inference/executor
proof goal. Branch / baseline: `research/simple-sub-intrusion` at
`396fe5335`. Authority: `docs/yulang-operational-type-safety-ja.tex:235-237,953-977`.
R12 is frozen at `tasks/agent-loop/inbox/paper-typing-subst-r12.md`, SHA-256
`1f8932d19129d02cd6e170890078db81cc4c810e203bf593b582ebeef696790a`.

## Fixed outcome

Expose one general type-level instance operation using the existing
`instantiateSubstitution`. Prove its commutation with arbitrary ambient
simultaneous substitution `σ`, using `instantiateSubstitution_commutes` and
`subst_comp`, with exact de Bruijn lifting. Apply this shared result to exactly
three represented typing forms:

- `roll(v) : μ α.T` when `v : T[μ α.T/α]`;
- `unroll(v) : T[μ α.T/α]` when `v : μ α.T`;
- type application of a value typed at `∀ α.T`, producing `T[A/α]`.

Use the existing `Ty.mu`, `Ty.poly`, `Value.roll`, `Value.typeApplication`,
and `Computation.unroll` constructors. Preserve the distinction between
ambient `σ` and the one-binder instance substitution; no equality may collapse
`μ` or `∀` types. Type abstraction introduction and its freshness premise,
recursive value graph guards, and every other omitted constructor remain out of
this slice. Extend the mutual transport proof and audit its exact theorem types
and complete axiom dependencies.

## Exact ownership and dependencies

Primary `/root` owns:

- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`
- this contract, `tasks/agent-loop/current.json`, and
  `tasks/agent-loop/inbox/paper-typing-subst-r13.md`
- `notes/theory/lean/.lake/R13Audit.lean`,
  `notes/theory/lean/.lake/R13InstantiationProbe.lean`, and primary cache

Read-only: `DeclSubst.lean`, `PaperTypeSubstitution.lean`,
`PaperTypeFormation.lean`, cited paper clauses, and frozen R12 handoff. Eight
historical/foreign UNKNOWN reservations stay quarantined. No child or reviewer
is admitted; R9-R12 independent review remains `NOT_RUN`. The Rust lane remains
`NO_SAFE_CODE_SLICE`: the `program.rs`/`machine.rs` correspondence gap is still
open and no implementation behavior is authorized by this proof slice. Keep
Rust/native and production files out of scope.

Input hashes:

- `PaperExecutionSyntax.lean`: `0d5da86660c4daa4bd8afb6651957a43ee6dc1d18dab774b107a5ba612844616`
- `PaperExecutionTypingSubstitution.lean`: `1f78031b5dc4ca493f2fbb47ff6a38297552bb22af3139b61d2662b32c3c067e`
- `PaperTypeSubstitution.lean`: `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861`
- `PaperTypeFormation.lean`: `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`
- `DeclSubst.lean`: `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`
- R12 handoff: `1f8932d19129d02cd6e170890078db81cc4c810e203bf593b582ebeef696790a`

## Resources, checks, stop conditions

Maximum 900 active seconds, 8 serial Lean/Lake invocations, and 120 checker
seconds; `-j1 -M1024`, one checker at a time. R12's 3 invocations and
approximately 11.5 seconds remain charged there and do not transfer. No tests,
Rust build, default-target build, or production edit. Build the focused typing
module and run the exact-type/complete-axiom audit. Stop on an off-by-one or
capture counterexample, wrong `unroll` index, type-algebra mismatch, unsafe
lease/dependency, user STOP, or budget limit. Never add `sorry`, `admit`,
project axioms, checker bypasses, hidden closure assumptions, or a premise that
identifies recursive and unfolded types.

## Acceptance and remaining boundary

Success requires focused syntax/typing builds; the shared instance/substitution
commutation theorem with arbitrary `σ`; all three new typing rules included in
six-family transport; exact printed types and full axiom audits for the shared
lemma, three rules, five public transport projections and mutual theorem; no
`sorryAx`, `_f`, failed declaration dependency or project axiom. Record the
specific paper-to-constructor mapping and all omitted cases in the handoff.

This remains a partial extrinsic judgment. Forall introduction/freshness,
recursive graph formation/guards, handlers and attempts, other omitted forms,
term substitution, owner alpha-renaming, complete paper typing,
inference/executor and original A/B obligations, source/native correspondence,
Rust bridges and independent review remain OPEN.
