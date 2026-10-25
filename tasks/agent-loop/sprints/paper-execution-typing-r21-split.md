# Sprint FULL-PAPER-TYPE-SUBSTITUTION-20261026/r21 — tuple split

Status: ADMITTED by Luna after R20 acceptance and sprint-end selector
consultation. Revision r1. Branch `research/simple-sub-intrusion`; baseline is
R20 accepted commit `b77fe13183e7ec80a95f08f919f34e832962c977`. Candidate proof
only; no semantic-adoption, Rust or production rights.

## Original parent and fixed outcome

The unchanged parent is manuscript
`docs/yulang-operational-type-safety-ja.tex:953–977`: simultaneous type
substitution for the full paper typing judgments and original source scope.
R21 adds the paper's tuple `split` elimination at line 229 to the represented
`PaperComputationTyped` judgment, proves raw-split inversion while retaining
the exact result type and arity, composes the rule with existing tuple-value
introduction, and proves arbitrary-σ transport for this new rule across all six
typing families. R18 variant type-argument correspondence remains OPEN and is
handled only by the separate primary intake cited below.

The paper rule says that `v : (Ā)` and the body has result `B` under
`Γ, x̄:Ā`; the conclusion is `split(v, x̄.M) : B` under the same shared
declaration table `D`, graph environment `Xi`, and tail `Γ`. The raw syntax is
`Computation.split tuple binders body` at
`PaperExecutionSyntax.lean:71–72`, with one ordered list of term names. The
value rule for tuples (`PaperExecutionSyntax.lean:656–659`) uses
`argsSyntax types` and `ValuesTyped` in source order.

Use the existing de Bruijn convention where a single right-appended paper
binder is represented by a cons at the head of `TypeEnvironment`. Therefore
the finite context extension for ordered component types `[A1, …, An]` is
`List.reverse [A1, …, An] ++ Γ`: the last source binder is index 0. Define one
named helper for this list extension, with a proved arbitrary-σ commutation
lemma. The split constructor must require
`binders.length = types.length`; it must type the scrutinee at exactly
`argsSyntax types` and the body at exactly the extended environment. No
`zip`-truncation, implicit binder count, reordered components, or separate
branch result is allowed. If the governing source or an existing context
convention contradicts this ordering, stop before the constructor is added.

## Exact outcome and evidence

Add the split constructor, a genuine inversion theorem for the raw `.split`, a
tuple-introduction composition theorem starting from `ValuesTyped`, and the
arbitrary-σ case in the existing common substitution recursor. Preserve the
six existing transport theorem statements and all previous constructors and
premises. The split recursor case must leave the binder-name list unchanged,
map the scrutinee and body under the same σ, map the component types in order,
preserve their arity, and transport the body environment by the helper lemma.

Success requires a focused build and complete type/axiom audits for the six
transport theorems, the split constructor, inversion, tuple composition and
environment-extension commutation lemma. The bundled audit validator must
pass; no `sorryAx`, project axiom, failed declaration/dependency, `sorry`, or
`admit` is allowed. The typing rule says nothing about executing the body.

Falsifiers include a one-element mismatch between binder/type lengths, reversed
payload-to-binder mapping, using `types ++ Γ` rather than the cons-derived
extension, a changed `D`, `Xi`, tail `Γ` or result type, a truncated list
combination, or a transport statement restricted to a special σ.

## Authority, baseline and dependencies

The governing typing source is manuscript line 229; the original parent and
its quantifiers are lines 953–977. R20 union elimination is an accepted
prerequisite in commit `b77fe13183e7ec80a95f08f919f34e832962c977`.

Frozen direct inputs at admission:
- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`:
  `678f84eb635c95392068887b834a4f79a1a754ad474b950097aa212a3b68032c`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`:
  `55c84a4c3a5e83c3f4b8ff05b836790f0357b836d31daf0b9b316c427947afb7`
- `notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean`:
  `568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a`
- `notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean`:
  `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861`
- `notes/theory/lean/YulangClosure/PaperTypeFormation.lean`:
  `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`
- `notes/theory/lean/YulangClosure/DeclSubst.lean`:
  `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`
- `docs/yulang-operational-type-safety-ja.tex`:
  `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`

No dependency or new semantic authority is introduced. The primary has
completed bounded source intake for R18 at
`tasks/agent-loop/inbox/r18-variant-authority-intake.md`; it found no authority
for the extra raw variant type-argument field, leaves that gate OPEN, and
grants no change to the variant domain. R21 is independent of that blocker.

## Proof and implementation lanes

- One registered `lean_prover` owns construction, inversion, composition,
  transport, audit source and one handoff in `/tmp/yulang-r21-split`.
- Luna owns the primary source intake, current state, final calls 7–8, one fresh
  independent review after freeze, adjudication, integration and Git.
- Implementation lane: `NO_SAFE_CODE_SLICE`. The bounded paper typing lemma
  does not authorize Rust changes; inspected HIR and runtime owners have no
  approved source-to-paper split mapping to implement here. No code semantics
  or Rust path is inferred from `split` typing.
- No Astra core assignment is warranted. No Sol counterexample lane is needed
  for this explicit syntax rule; the fresh reviewer independently checks the
  exact paper/environment correspondence and frozen Lean artifacts.

## Exact leases, resources and stop conditions

Worker leases only:
- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`
- `/tmp/yulang-r21-split/notes/theory/lean/.lake/R21Audit.lean`
- `/tmp/yulang-r21-split/tasks/agent-loop/inbox/paper-typing-subst-r21.md`

Dependencies are read-only; use the dedicated worktree cache. No wildcard,
extra scratch file, source/native mapping or semantic edit is leased. Primary
owns only this contract, `current.json`, its R18 intake, its final audit output,
the R20/R21 adjudication/history records, and the reviewed integration paths.

Maximum envelope: 900 active seconds overall, including primary R18 intake,
review and integration; at most 8 literal serial Lean/Lake invocations and 120
checker seconds. Worker calls 1–6 are construction and audit; primary calls
7–8 are final focused build and full audit. Each process counts, including a
failure. Run one at a time with `-j1 -M1024`; no reconnaissance/version-only
call, hidden retry, call transfer or inherited R20 budget. Review gets a fresh
non-author after the worker stops writing. No checker may launch until the
worker matches every frozen input and Luna records its actual active receipt.

Stop before adding a constructor if the binder ordering or tuple arity rule
cannot be grounded in the cited source/context convention, if any new premise,
dependency, lease or semantic choice is needed, at any checker failure, or at
the stated resource bound. Do not claim parent, execution, source/native or
production closure. The existing accepted union and wrap cases remain intact.

## Remaining gates

This packet closes only represented tuple split typing/inversion, tuple
introduction composition and arbitrary-σ support for those judgments. Full
paper substitution, R18 variant correspondence, nominal/switch/other omitted
rules, recursive graph guards, inference/executor semantics, original A/B,
source/native correspondence, Rust and production remain OPEN.
