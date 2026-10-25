# R22 primary adjudication — declared template invocation instance typing

Sprint `FULL-PAPER-TYPE-SUBSTITUTION-20261026/r22`, contract r1 SHA-256
`190841c2881a73ad66e9461642486bd01111cf9c037ea4bac28c7e60ef62b54b`.
Frozen R21 baseline `8ff731456dd9385f6497e9c5c0b99e7d8820a898`; checked candidate commit
`5fb19dddc9a3d49c0b680618cf09bbd5fb0f992e`.

## Disposition

**R22 accepted as a checked, independently reviewed prerequisite.** The represented
paper template invocation now resolves one complete declaration entry by identity,
requires exact type-argument arity, types all actual values against the formal list
instantiated by the invocation's one type-argument vector, and returns the result
instantiated by that same vector. Inversion retains the same declaration witness and
exact result index. The arbitrary-σ common transport carries resolution, actual
argument typing, every formal and the result together, while declaration mapping
preserves the executable code body. All six existing public transport statements
remain unchanged.

Paper `docs/yulang-operational-type-safety-ja.tex:129,243,953–977` is the governing
source. The separate table-body condition remains OPEN: this result does not construct
the registered body's derivation under its prescribed formal environment, instantiate
or execute that body, or establish preservation. Full-paper substitution, R18 variant
correspondence, omitted rules, recursive graph guards, inference/executor semantics,
original A/B, source/native/Rust and production remain OPEN. No semantics or accepted
source domain changed.

## Frozen artifacts and independent review

- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`, SHA-256
  `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`.
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`, SHA-256
  `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41`.
- Exact audit `notes/theory/lean/.lake/R22Audit.lean`, SHA-256
  `ff63bb4a3a557699c7a88beca4d26008f7f71039eaa066a6324c4f1ae309182c`.
- Worker handoff `tasks/agent-loop/inbox/paper-typing-subst-r22.md`, SHA-256
  `b41e72765894a205d4eac7a27f14a61e5cf3dce4bced059e55ba8b175a228356`.
- Primary pinned build/audit output `tasks/agent-loop/inbox/paper-typing-subst-r22-primary-verification.txt`, SHA-256
  `64ffb5bae31657a0f4302a482a988c48203057bc6b0710fda4b4f3be4ae94290`.
- Fresh independent source/spec review
  `tasks/agent-loop/inbox/paper-typing-subst-r22-review.md`, SHA-256
  `a48c28ffefa97c39b73815530e13f7e70d88e2fdc1f9c8da2c329008f8e11975`.
  Verdict: **NO BLOCKING, MAJOR OR MINOR FINDINGS**. Reviewer `/root/r16_independent_review`
  was not an author or repairer, confirmed exact artifact/dependency hashes and the
  audit/type/axiom correspondence, and used zero Lean/Lake calls. Reviewer is STOPPED;
  report is frozen.

The review report describes `.lake/R22Audit.lean` as an ignored scratch file not
claimed as a separately committed source blob. That packaging detail is inaccurate:
`git ls-tree 5fb19dddc9a3d49c0b680618cf09bbd5fb0f992e` confirms that exact audit path
is included in the frozen candidate commit. Its reported and committed byte hash is
the same. This correction does not change the source review or kernel result.

## Checker receipts and limits

Pinned native Lake/Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
Primary calls 1–2 queried exact native tool versions (both exit 0); call 3 built
`PaperExecutionSyntax` and `PaperExecutionTypingSubstitution` (exit 0, all 7 jobs);
call 4 ran `.lake/R22Audit.lean` (exit 0). Bundled `validate_audit` passed all ten
complete, ordered theorem type/axiom records. `PaperComputationTyped.template` reports
no axioms. Each of the ten audited theorem declarations reports exactly
`[propext, Quot.sound]`. No `sorryAx`, project axiom, `Classical.choice` or disallowed
axiom appears. The six-module dependency-cone escape-token scan found no
`sorry`/`admit`/`axiom`/`native_decide`/`debug.skipKernelTC` matches.

Total: 4/8 permitted literal calls including version receipts; two build/audit calls;
worker 0 calls/cache writes; reviewer 0 calls. The wrapper did not retain exact
process elapsed time, so this record reports no invented duration. The 120 checker
second cap was not exceeded. No default/full build, Rust build, tests or network work
was run.

## Parent application and first remaining premise

R22 supplies the represented type-instance rule and its arbitrary-substitution
preservation under explicit premises: a unique complete entry, exact type arity and
`ValuesTyped` actual arguments. It does not prove those premises for every concrete
source or establish whole-table validity. The first remaining template execution
premise is to type the resolved stored body in the formal environment prescribed by
paper :129, then establish type/body instantiation and execution correspondence. Owner:
primary/source-proof intake under a new exact packet.

R18's extra raw variant type-argument correspondence remains OPEN and UNADOPTED; the
separate v1 docket is only a proposal for authority review. R22 does not consume it.
