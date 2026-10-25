# Paper execution typing substitution — r4

Status: renewed primary-only construction. Keep the original parent and full
paper scope; r1–r3 remain preserved history.

## Parent and exact output

Prove the paper's simultaneous type-substitution lemma at
`docs/yulang-operational-type-safety-ja.tex:953–977`, item 2, for the full
syntactic execution typing judgments; preserve downstream `thm:safety` at line
1140 and the user's full type-inference/executor objective. Every constructor
in `tasks/agent-loop/inbox/paper-typing-subst.md` remains required. No generic
preservation premise, assumed substitution result, or `Bad` typing is allowed.

The constructor-complete raw syntax and substitution traversal is
`notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`. The substitution
proof output is
`notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`.
Reconcile the former `PaperTypingSubstitution.lean` lease to that exact path.

## Results carried forward

R3 raw syntax traversal compiles under the pinned Lean 4.35.0 toolchain. The
first partial judgments for variables, graph references, literals, tuples,
sequences, delays, lambdas, injections, same-value intersection, top/view,
return, let, force, call and failure are source-grounded but not complete. The
latest check failed because the environment was a fixed mutual-inductive
parameter; lambda/let require it as an index. R4 moves each environment into
the judgment index. Preserve the omitted-rule list in the handoff, including
records, variants, nominal declarations, recursive values/graphs and guards,
operations/handlers/mappers, primitives/templates, patterns, continuations,
all administrative forms and the 62 fixed primitive signatures.

Replace `ValueGraph.guarded : Prop` with the actual paper guard before graph
coverage. Keep declaration identity, same `Xi` across premises, operation
instance payload/response equality, binder lifting and same-underlying-value
intersection evidence. A compiling partial judgment is not parent closure.

## Work mode and verification

Primary owns shared files and Lake cache. Eight UNKNOWN reservations remain
quarantined; no worker/reviewer/Astra/Rust/native process is admitted. Continue
with the environment-index repair, then add all paper judgments and prove the
simultaneous substitution theorem by mutual derivation induction, applying the
r5 declaration-instance lemma at operation cases. Freeze exact first missing
case if the full parent remains open.

R1 and r2 call/checker overages are charged. R3 used four serial Lean commands
(about 27 checker seconds); raw syntax traversal compiled, while the first
judgment layer failed on the fixed-environment parameter. R4 allows at most
900 primary active seconds, eight serial Lean calls and 120 cumulative Lean
checker seconds, reduced to reconciled available resources. Build/check only
after a coherent source edit; preserve complete diagnostics and actual tool
versions. Fresh independent review is required before promotion.

Run `python3 tools/agent_sprint.py check` for state consistency. Static checks
are not mathematical verification. The active output paths are this contract,
`PaperExecutionSyntax.lean`, `PaperExecutionTypingSubstitution.lean`,
the existing handoff and primary-owned `current.json`.
