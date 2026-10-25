# R21 primary adjudication — tuple split typing and substitution

Sprint `FULL-PAPER-TYPE-SUBSTITUTION-20261026/r21`, contract r1 SHA-256
`7bdab04134682ce01ebf723010c26a4d3a896cf2d024c8df0384f25cdc44d5ad`.
Frozen baseline: R20 accepted checkpoint
`b77fe13183e7ec80a95f08f919f34e832962c977`.

## Disposition

**R21 accepted as a reviewed prerequisite.** The represented paper computation
judgment now includes tuple `split` elimination, with an explicit binder/type
arity equality and a finite ordered environment extension. A genuine inversion
retains the original result-type index, tuple introduction composes with the
rule from ordered `ValuesTyped`, and the common arbitrary-σ substitution proof
transports the new case. All six transport theorem statements remain intact.

This follows manuscript `docs/yulang-operational-type-safety-ja.tex:229`:
`v : (Ā)` and the body has result `B` under `Γ, x̄:Ā`, with the same `D`,
`Xi`, and tail `Γ`. Ordered component types `[A1, …, An]` extend the Lean
de Bruijn environment as `reverse types ++ Γ`. This repeats the existing
single-binder convention: a right-appended binder is consed at the head and
lookup index zero selects that latest binder. The last source component is
therefore at index zero. `extendTupleEnvironment` states this explicit list
extension, and its substitution commutation lemma uses arbitrary σ without a
formation or closedness premise. The raw binder-name list is preserved.

R21 closes only represented split typing/inversion, tuple-introduction
composition, and arbitrary-substitution support for these judgments. It proves
no body execution, term substitution, source-name/de-Bruijn resolution, native
tuple binding, inference/executor safety, or production fact. R18's extra
variant type-argument correspondence remains OPEN; the separate primary intake
found no governing definition and selected no interpretation. Full-paper
substitution, omitted rules, recursive graph guards, original A/B, source/native
correspondence, Rust and production remain OPEN.

## Frozen artifacts and independent review

- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`, SHA-256
  `e025922217e5c5fc6d68780936acd99ac8252267f8c262b50da790a72cf73b0e`.
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`,
  SHA-256 `db213de9e97d965fb5e105f75009c9ec4f64e02892e5fdf3a8132317cc5e5f1d`.
- Worker handoff `tasks/agent-loop/inbox/paper-typing-subst-r21.md`, SHA-256
  `1ab3773ae5d71b877f124c7bfc3ba96ab39bdc52df9cb588a0d4de5ab99a623d`.
- Exact worker audit source
  `tasks/agent-loop/inbox/paper-typing-subst-r21-audit.lean`, SHA-256
  `6c612cd3a4025e2e8b709ce1ec32090bfc82de48c0e25fb86d88c64ee6cc93d7`.
- Complete primary final build/audit output
  `tasks/agent-loop/inbox/paper-typing-subst-r21-primary-verification.txt`,
  SHA-256 `6188acac1bdd0a77b80a05e4b970aa874b107688e4c4c390ea0dd3584838f440`.
- Fresh independent source-only review
  `tasks/agent-loop/inbox/paper-typing-subst-r21-review.md`, SHA-256
  `516eaa6b4303cc00ddfe5a2efae2392183fcc4e83fde0a8986aaa5bcde3d7c20`.
  Verdict: **NO BLOCKING OR MAJOR FINDINGS**. The reviewer checked manuscript
  correspondence and binder order, exact arity, shared contexts, inversion and
  result retention, tuple composition, all six transports, complete axiom
  output, dependency hashes and proof-escape tokens. It used zero Lean/Lake
  calls and is not a fresh kernel receipt.

The worker froze both source modules, audit and handoff before review. Reviewer
was not an author or repairer and reviewed fixed commit
`c62673066ae9c366f150ec1cffa13a44f2f2a877`. Reviewer cessation was confirmed;
there are no remaining writer processes or descendants.

## Checker receipts and limits

- Worker invocation 1: focused build of `PaperExecutionSyntax` and
  `PaperExecutionTypingSubstitution`; exit 0, 21.260374 seconds.
- Worker invocation 2: `lake env lean -j1 -M1024 .lake/R21Audit.lean`; exit 0,
  0.651341 seconds. Bundled `audit_source/validate_audit` passed. Eight audited
  theorems report exactly `[propext, Quot.sound]`; the environment-extension
  theorem reports `[propext]`; the split constructor has no axioms.
- Primary invocation 7 repeated the focused build against the integrated frozen
  bytes. The complete retained output ends `Build completed successfully (7
  jobs)`. The wrapper did not retain the process exit code or exact elapsed
  time separately; no extra call was spent to reconstruct it. The worker's
  independent focused build exited 0.
- Primary invocation 8 ran the exact audit source with
  `lake env lean -j1 -M1024`; exit 0, 2.108447 seconds. The complete output is
  retained above and reports the same nine theorem type/axiom results.
- Total: four of eight permitted literal Lean/Lake processes. Exact measured
  checker time is 21.911715 seconds for worker calls 1–2 plus 2.108447 seconds
  for primary call 8; primary call 7's unretained exact duration was under its
  configured 30-second wait. Total is therefore below 54.020162 seconds of
  the 120-second cap. Worker calls 3–6 were unused. No budget was transferred.
  Active-time telemetry is unavailable.

No checker failure or failed declaration is hidden. The retained audit has no
`sorryAx`, project axiom, `Classical.choice`, or disallowed axiom. No source,
dependency, semantic scope, Rust, or production change was made beyond the two
leased Lean files.

## Remaining proof gates

R21 does not close the original full-paper simultaneous-substitution theorem.
R18 variant correspondence is still the first unresolved paper-order
introduction. Nominal, switch, other omitted forms and recursive graph guards
remain open. Inference/executor semantics, original A/B, source/native and
production require their separate original-source and implementation evidence.
This adjudication grants no follow-on worker lease; the next action is selected
at the sprint-end dispatcher boundary against the current source/authority
state.
