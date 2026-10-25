# Paper execution syntax and typing substitution — r3

Status: active primary-only construction. Revision 1 and revision 2 remain
historical failure records. The parent theorem and full paper scope are
unchanged.

## Parent and source obligations

Parent: `docs/yulang-operational-type-safety-ja.tex:953–977`, item 2;
downstream `thm:safety` at line 1140. Continue toward all paper execution
typing judgments and the simultaneous type-substitution induction. Every rule
in `tasks/agent-loop/inbox/paper-typing-subst.md` remains in scope. No generic
preservation premise or assumed substitution result is allowed.

## Inputs and naming

Branch `research/simple-sub-intrusion`; baseline `e0294daf8361ab012bdd70daba33e24947355fb5`.
Paper and dependency hashes are frozen in revision 1. Revision 2 diagnostics
and failed source remain at their recorded paths and hashes. The syntax source
is now named `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`,
which describes its present content more accurately than `PaperTyping.lean`.

## Revised termination method

For every recursive traversal through a list, destructure the attached entry
into its value and membership proof in the callback, and name the proof there.
Use that proof directly with `List.sizeOf_lt_of_mem`. For record fields and
recursive bindings, add proved projection inequalities for product components;
for optional default/guard bodies, prove the `some` payload is no larger than
the containing option. Chain these facts with the enclosing constructor's
size equation. Keep the measure on the original syntax object, unchanged by
`liftSub` and `liftSubN`.

Before checking, inspect every recursive list/option call and write down its
complete strict-subterm chain. Do not repeat tactic-only substitutions before
that inspection. Then check the complete syntax module and continue to the
actual typing judgments within this envelope. The syntax traversal alone does
not meet the parent outcome.

## Accounting and limits

Revision 1 exceeded its six-call cap (nine calls, about 25 checker seconds).
Revision 2 used four additional serial Lean invocations (about 17 checker
seconds); the complete syntax module still fails termination. Both grants are
charged. This revision allows at most 300 additional primary seconds, four
serial Lean calls and 60 cumulative checker seconds, whichever ends first.
No child/reviewer/Astra/Cargo/native process is admitted; eight UNKNOWN
reservations remain quarantined. Independent review is required before
promotion.

## Artifacts

- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`
- `tasks/agent-loop/inbox/paper-typing-subst.md`
- this contract
- primary-owned `tasks/agent-loop/current.json`
- checker receipt `/tmp/yulang-paper-typing-subst-r1-check.log`
