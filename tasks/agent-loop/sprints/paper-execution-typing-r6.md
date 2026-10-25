# Sprint FULL-PAPER-TYPE-SUBSTITUTION-20261025/r6 — record typing bridge

Status: issued by the primary after the R5 resource checkpoint.
Branch: `research/simple-sub-intrusion`; R6 setup is a records-only child of
`c82efbfbe5e944adeeca0e29835f77087c9cb384`. The proof worktree must use the
R6 setup commit and the frozen source hashes below.
Authority: `docs/yulang-operational-type-safety-ja.tex`, §types pp. 8–10,
especially record formation/field/lookup rules around lines 217–231, and the
record code lemma at lines 724–749. Parent substitution claim remains lines
953–977, item 2; downstream safety theorem remains line 1140.

## Original outcome and success evidence

Preserve the original full paper typing judgment and simultaneous type
substitution theorem, all constructors, quantifiers, and source domain. R5
established a kernel-checked theorem only for its partial judgment (13 value
constructors, five computation constructors, and list rules); it did not
close the paper theorem, source correspondence, executor safety, or any A/B
parent. R5 used 7/8 Lean/Lake calls; all prior R1–R5 resource charges remain.

R6 targets one source-faithful bridge: represent record values, required-field
projection, and declared optional lookup in the extrinsic judgments, then apply
simultaneous substitution to those new cases. Preserve `Presence`, the
paper's required-label subset/domain/declaration conditions, field payload
types, and the existing `RecordFormed` uniqueness/formation evidence where
applicable. Do not impose list-order equality, erase optional absence, invent
field evidence, or restrict accepted records. Keep `Bad` untypable.

Success is a checked focused build and exact type/axiom audit for the extended
mutual substitution result and its support lemmas, plus an explicit rule-to-Lean
map showing which record premises are represented. The falsifiers are a
missing optional field rejected, an undeclared field accepted, a required field
missing accepted, a payload type mismatch accepted, or substitution changing
labels/presence/declaration identity. Report the first obstruction rather than
strengthening assumptions. The parent remains OPEN until every other paper
constructor and shared index is represented and independently reviewed.

Frozen inputs at admission:

- paper: `docs/yulang-operational-type-safety-ja.tex` —
  `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`
- syntax: `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean` —
  `2c2f7efac389488cdebee22fb5c6c666b183f7c200fd3ffec73c9c2fb41ae81d`
- typing/substitution: `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean` —
  `f29c00981f9abaf29051021570088b77cc031b191d9429f7e15d4210f992a313`
- formation: `notes/theory/lean/YulangClosure/PaperTypeFormation.lean` —
  `e090a4674fcdac27dc73b50b8a0f32c65618c81d1ccd350648319ecfb4a1f454`
- type substitution: `notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean` —
  `a2faf4dc7765724cd033fd1014b0acb0e87c58902ac71ede157d2e268ba7ad83`

## Lanes and exact permissions

1. Proof lane: one `lean_prover` works in a detached R6 worktree under
   `/tmp/yulang-r6-paper-record-proof`. It may edit only
   `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`,
   `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`,
   and `tasks/agent-loop/inbox/paper-typing-subst-r6.md` in that worktree.
   It owns that worktree's `.lake` build/cache and scratch files. It does not
   commit, push, edit shared state, source code, tests, manifests, or other
   records. Freeze writes and report actual hashes before returning.
2. Complementary source/spec lane: one researcher performs a read-only audit of
   the exact paper record/field/lookup rules and the Rust construction/consumer
   path. It returns findings in its message, with source locators and concrete
   falsifiers. It has no file lease, build, or Git permission.
3. Primary: owns this contract, current state, integration and Git. The primary
   applies an accepted patch in the main checkout, checks it against the frozen
   inputs, and owns final build/audit. No production compiler change is
   authorized. There is `NO_SAFE_CODE_SLICE` for R6.

Do not reclaim or overlap any of the eight historical/foreign UNKNOWN leases.
The proof lane is isolated in a detached worktree; no agent gets a path in the
main checkout. The complementary lane is read-only. If either launch or
capacity observation fails, record the actual failure and continue only within
the remaining primary allocation; never invent a worker receipt.

Resources: total primary+proof budget <=900 active seconds, <=8 serial
Lean/Lake invocations across worker and primary, and <=120 cumulative checker
seconds. Proof lane <=6 invocations / 80 checker seconds / 600 active seconds;
primary integration <=2 invocations / 40 checker seconds / 240 active seconds.
Research lane <=180 active seconds and no Lean/Lake invocation. Pinned Lean
4.35.0, `-j1 -M1024`; one verification owner at a time. R1–R5 charges are
retained. No Astra assignment. Fresh independent review is NOT_RUN and must be
assigned only after the result is frozen and capacity/lease checks permit.

Continue within this envelope through record evidence, field/lookup cases,
mutual substitution, checker audit, and source/spec adjudication. Stop at the
first mathematical counterexample, authority/dependency change, resource
limit, or user STOP. Consult the dispatcher at a material boundary; it does
not launch workers or own status/Git.

## Parent application and residual scope

The new theorem cases must transport the same `σ` through declaration table,
graph types, term environment, syntax and result type, preserving raw field
labels and presence. Use existing type substitution and `RecordFormed` results
only under their actual hypotheses. This slice does not cover variants,
nominal declarations, guarded recursive graphs, primitives/templates,
patterns, handlers/operations, mappers, continuations, administrative forms,
or all thirteen source expressions. Those remain explicitly OPEN.

Review target: exact frozen Lean diff and its source-to-rule map; the proof
author and source researcher are not eligible to certify their own artifacts.
Acceptance requires a fresh independent reviewer, exact theorem types and
axioms, represented/omitted constructor list, and no hidden assumptions. The
primary owns record synchronization, status, commit, outbound-range inspection
and normal push.
