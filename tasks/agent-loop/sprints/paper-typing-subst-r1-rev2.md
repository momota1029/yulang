# Paper execution typing substitution — r1 revision 2

Status: renewed primary-only construction; revision 1 is preserved as the
overrun/failure record. Parent theorem, dependencies, artifact paths and full
paper scope are unchanged.

## Parent and inputs

Paper `docs/yulang-operational-type-safety-ja.tex:953–977`, item 2; downstream
`thm:safety` at line 1140. Preserve the complete original inference/executor
goal. Baseline `157548a2ba67d5cd2c3bc53e9f7a447d8249d9a6` on
`research/simple-sub-intrusion`. Revalidate frozen input hashes recorded in
revision 1 before further work. Preserve the revision 1 failed source bytes:
SHA-256 `a89201a928d3fbc02cff8ca99c45ae9f75fba813fe4b73b2bc9ba5bcaf09958e`.

## Changed proof method

Keep the raw syntax and explicit substitution maps. Before any further Lean
call, replace recursive `List.map` callbacks over syntax with membership-carrying
traversals such as `List.attach.map`/`List.pmap`. For each recursive call,
derive strict decrease from the attached membership proof, the product-field
size inequality, and the enclosing constructor's size equation. Use explicit
`none`/`some` cases for `Option` children where that exposes the subterm.
The measure depends only on the syntax object; changing the type substitution
to `liftSub` or `liftSubN` does not alter the measured object.

Do not use fuel/fallback traversal, `partial`, an assumed map law, or a generic
typing-substitution premise. After every recursive call has an explicit
strict-subterm argument, check the complete syntax module. Continue under this
same contract to the paper typing judgments and actual mutual-induction cases.
The sprint goal still requires all constructors in the frozen rule inventory,
not merely a compiling traversal. At the bound, freeze the exact unclosed
termination or typing case and keep the parent theorem OPEN.

## Accurate resource and result accounting

Revision 1 executed nine serial Lean calls (about 25 checker seconds) against
its six-call limit; preserve this overrun. Its earlier grant is charged and is
not restored. Revision 2 grants at most 300 additional primary seconds, at
most four serial Lean calls, and at most 60 cumulative checker seconds,
whichever ends first. The first call is permitted only after all membership
traversals and proposed decrease arguments have been written and source
inspected. Preserve full diagnostics at
`/tmp/yulang-paper-typing-subst-r1-check.log` and module output at
`/tmp/yulang-paper-typing-subst-r1.olean`.

Eight prior UNKNOWN reservations remain quarantined. No child, reviewer,
Astra, Rust/Cargo or native process is admitted. Independent review is still
required before promotion.

Exact outputs remain `notes/theory/lean/YulangClosure/PaperTyping.lean`,
`notes/theory/lean/YulangClosure/PaperTypingSubstitution.lean`,
`tasks/agent-loop/inbox/paper-typing-subst.md`, this revision, and primary-owned
`tasks/agent-loop/current.json`.
