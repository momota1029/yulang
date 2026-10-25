# Sprint PAPER-TYPE-BETA-EXECUTION-20261026/r54

Status: ASSIGNED. This is a fresh proof-repair sprint after R53 stopped at its
two-construction-failure bound. It preserves the manuscript-explicit type-beta
claim and does not ask about, answer, or adopt either withdrawn semantic
question.

Branch: `research/simple-sub-intrusion`
Baseline: `86f88fccc179cd640a81372a0359a27d1bc1b569`
Authority: `docs/yulang-operational-type-safety-ja.tex` lines 1101 and
2063–2065; corrected account `notes/theory/2026-10-24-corrected-core-value-continuation.md`
V1(b). The target remains preservation of the existing represented judgments
under the explicit administrative step `(Λα.v)[A] → v[A/α]`. Preserve the
original constructors, shared contexts, theorem statements, and quantifiers.

## R53 evidence used as an unaccepted repair seed

- Candidate `PaperTypeBetaExecution.lean`, SHA-256
  `6181de0b6cc8bccf456c7649662b8fc0f7486e98ff3bb2b44a4871f7cb7c7315`.
- Unexecuted audit template SHA-256
  `618e2d5c5efba224b22a754d73f562466bf14d3e016263ebe448b955936d7e1f`.
- Handoff SHA-256
  `5258547ca02c64666a0d25166779ea3d0ee6515bf4ed65c53e33122755e68db6`.
- R53 had two construction failures and no accepted theorem. Its candidate,
  audit, or statements are not trusted results; re-open and repair them in the
  new isolated baseline. Keep all R53 frozen evidence read-only.

## Fixed dependencies

The following Lean source hashes were verified for R53 and must be verified
again against this baseline before construction:

- `PaperExecutionBinderLaws.lean` `568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a`
- `PaperExecutionTypingSubstitution.lean` `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41`
- `PaperTypeSubstitution.lean` `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861`
- `PaperExecutionSyntax.lean` `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`
- `PaperTermSubstitution.lean` `a4f87f9604c03beefdc44de5d45fcd9f5924ca9580c75edf353cf267e69a0d4f`
- `DeclSubst.lean` `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`
- R49 `PaperPerformLetExecution.lean` `2f0026049554cb870158115b4bab8d42f7cbee8b030ee3f84a904763c328cac0`
- `lean-toolchain` `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`
- `lakefile.toml` `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194`
- `lake-manifest.json` `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`

## Required proof work

Use isolated exact-baseline copy `/tmp/yulang-r54-type-beta-repair`; no
repository source edits. Repair all three R53 proof-state failures without
dropping constructors or strengthening hypotheses:

1. Replace the unavailable `forall_true_left` rewrite in `map_attach_eq_iff`.
   Prove both directions explicitly by introducing the attached element and
   membership witness, then eliminate the trivial `True` premise.
2. In `CancelAt`, handle `PatternPlan.record` explicitly. Unpack both nested
   membership witnesses for `fields.attach.attach`; split each optional
   default into `none`/`some`, recover the original field membership, derive
   the size decrease, and apply the corresponding structural induction
   hypothesis to the pattern and default computation.
3. In `mapGraphEnvironment_cancel`, prove the simplified pointwise membership
   goal directly. Do not change it to list equality after simplification.

Then close raw cancellation for every existing Value, Computation,
PatternPlan, ConstructorBranch, GuardedBranch, ValueArm, OperationArm,
HandlerPlan and MapperPlan constructor; close ambient cancellation for the
entire declaration table including template bodies beneath formal binders;
and close graph/type environment cancellation. Apply these results to the
existing `PaperValueTyped.subst_explicit` theorem. Preserve arbitrary shared
`D/Ξ/Γ`, distinct type argument/body/result types, nested forall/μ cases and
all template bodies. Finish `typeBetaValue` applicability/preservation and
the distinct beta-then-force path `force_typeBeta_delay` with preservation at
each step.

Success requires a building candidate, strict audit of every declared theorem
in the module (declaration kind, complete type, full `#print axioms`; whitelist
only `{propext, Classical.choice, Quot.sound}`), primary root build/audit,
and fresh independent compiler review. A helper lemma alone is not success.
Do not add axioms/sorry, assume cancellation, restrict to empty/closed
contexts, or change public statements. Any such required weakening stops the
packet and returns the exact obstruction. Source/native realization, full
executor, inference A/B, and production remain OPEN.

## Roles, exact outputs, and resources

One registered `lean_prover`, no descendants and no Astra. R54 baseline and
all source/toolchain pins are rechecked before it writes. R53 seed is read-only.
Worker writes only inside the isolated checkout: the candidate module;
`.lake/R54Audit.lean`, `.lake/R54Probe.lean`, `.lake/R54run.py`, `.lake/R54-origin.json`,
`.lake/R54-stop.json`, `.lake/R54-artifacts.json`, `.lake/R54-call-01.json`
through `R54-call-10.json` with each matching `.stdout` and `.stderr`,
`.lake/R54-candidate-failure-01.lean` and `-02.lean` when applicable, and the
single handoff `tasks/agent-loop/inbox/paper-type-beta-r54.md`. Lake's isolated
`.lake/config` and `.lake/build` outputs belong to this worker/cache only; no
shared cache use. Python must use `-B` / `PYTHONDONTWRITEBYTECODE=1`. Preserve
incidental R53 pycache; do not delete it.

Resources: worker 1200 active seconds / 10 literal calls / 120 checker seconds;
Luna primary 420 seconds / 4 calls / 60 checker seconds; fresh independent
reviewer 180 seconds / zero checker calls; aggregate 1800 seconds / 14 calls /
180 checker seconds. R54 primary clock origin was captured before setup at UTC
`2026-10-25T22:03:50Z`, monotonic `47137670652204 ns`; charge setup, pin
verification, handoff freeze and integration to this grant. Worker captures
its monotonic origin before initial reads. Resolve native Lake and check both
Lake and `lake env lean --version` against Lean 4.35.0. Use `-j1 -M1024`, keep
complete stdout/stderr, exact argv/cwd/exit and monotonic duration. The first
build must include the candidate. Stop at two construction failures, any
authority/input mismatch, any failed final audit/build, timeout, or cap.

No tests or implementation work are authorized. `NO_SAFE_CODE_SLICE` stands.
Only after a frozen candidate, complete audit, CLEAN independent review and
Luna adjudication may Luna integrate byte-identical module plus exactly one
root import. The two withdrawn question directories remain untouched,
unstaged, uncommitted and semantically unresolved; legacy UNKNOWN leases remain
quarantined.

- `.lake/build/ir/YulangClosure/DeclSubst.c`
- `.lake/build/ir/YulangClosure/DeclSubst.c.hash`
- `.lake/build/ir/YulangClosure/DeclSubst.setup.json`
- `.lake/build/ir/YulangClosure/PaperCoreStep.c`
- `.lake/build/ir/YulangClosure/PaperCoreStep.c.hash`
- `.lake/build/ir/YulangClosure/PaperCoreStep.setup.json`
- `.lake/build/ir/YulangClosure/PaperExecutionBinderLaws.c`
- `.lake/build/ir/YulangClosure/PaperExecutionBinderLaws.c.hash`
- `.lake/build/ir/YulangClosure/PaperExecutionBinderLaws.setup.json`
- `.lake/build/ir/YulangClosure/PaperExecutionGraphWeakening.c`
- `.lake/build/ir/YulangClosure/PaperExecutionGraphWeakening.c.hash`
- `.lake/build/ir/YulangClosure/PaperExecutionGraphWeakening.setup.json`
- `.lake/build/ir/YulangClosure/PaperExecutionSyntax.c`
- `.lake/build/ir/YulangClosure/PaperExecutionSyntax.c.hash`
- `.lake/build/ir/YulangClosure/PaperExecutionSyntax.setup.json`
- `.lake/build/ir/YulangClosure/PaperExecutionTypingSubstitution.c`
- `.lake/build/ir/YulangClosure/PaperExecutionTypingSubstitution.c.hash`
- `.lake/build/ir/YulangClosure/PaperExecutionTypingSubstitution.setup.json`
- `.lake/build/ir/YulangClosure/PaperTermSubstitution.c`
- `.lake/build/ir/YulangClosure/PaperTermSubstitution.c.hash`
- `.lake/build/ir/YulangClosure/PaperTermSubstitution.setup.json`
- `.lake/build/ir/YulangClosure/PaperTypeBetaExecution.c`
- `.lake/build/ir/YulangClosure/PaperTypeBetaExecution.c.hash`
- `.lake/build/ir/YulangClosure/PaperTypeBetaExecution.setup.json`
- `.lake/build/ir/YulangClosure/PaperTypeFormation.c`
- `.lake/build/ir/YulangClosure/PaperTypeFormation.c.hash`
- `.lake/build/ir/YulangClosure/PaperTypeFormation.setup.json`
- `.lake/build/ir/YulangClosure/PaperTypeSubstitution.c`
- `.lake/build/ir/YulangClosure/PaperTypeSubstitution.c.hash`
- `.lake/build/ir/YulangClosure/PaperTypeSubstitution.setup.json`
- `.lake/build/lib/lean/YulangClosure/DeclSubst.ilean`
- `.lake/build/lib/lean/YulangClosure/DeclSubst.ilean.hash`
- `.lake/build/lib/lean/YulangClosure/DeclSubst.olean`
- `.lake/build/lib/lean/YulangClosure/DeclSubst.olean.hash`
- `.lake/build/lib/lean/YulangClosure/DeclSubst.trace`
- `.lake/build/lib/lean/YulangClosure/PaperCoreStep.ilean`
- `.lake/build/lib/lean/YulangClosure/PaperCoreStep.ilean.hash`
- `.lake/build/lib/lean/YulangClosure/PaperCoreStep.olean`
- `.lake/build/lib/lean/YulangClosure/PaperCoreStep.olean.hash`
- `.lake/build/lib/lean/YulangClosure/PaperCoreStep.trace`
- `.lake/build/lib/lean/YulangClosure/PaperExecutionBinderLaws.ilean`
- `.lake/build/lib/lean/YulangClosure/PaperExecutionBinderLaws.ilean.hash`
- `.lake/build/lib/lean/YulangClosure/PaperExecutionBinderLaws.olean`
- `.lake/build/lib/lean/YulangClosure/PaperExecutionBinderLaws.olean.hash`
- `.lake/build/lib/lean/YulangClosure/PaperExecutionBinderLaws.trace`
- `.lake/build/lib/lean/YulangClosure/PaperExecutionGraphWeakening.ilean`
- `.lake/build/lib/lean/YulangClosure/PaperExecutionGraphWeakening.ilean.hash`
- `.lake/build/lib/lean/YulangClosure/PaperExecutionGraphWeakening.olean`
- `.lake/build/lib/lean/YulangClosure/PaperExecutionGraphWeakening.olean.hash`
- `.lake/build/lib/lean/YulangClosure/PaperExecutionGraphWeakening.trace`
- `.lake/build/lib/lean/YulangClosure/PaperExecutionSyntax.ilean`
- `.lake/build/lib/lean/YulangClosure/PaperExecutionSyntax.ilean.hash`
- `.lake/build/lib/lean/YulangClosure/PaperExecutionSyntax.olean`
- `.lake/build/lib/lean/YulangClosure/PaperExecutionSyntax.olean.hash`
- `.lake/build/lib/lean/YulangClosure/PaperExecutionSyntax.trace`
- `.lake/build/lib/lean/YulangClosure/PaperExecutionTypingSubstitution.ilean`
- `.lake/build/lib/lean/YulangClosure/PaperExecutionTypingSubstitution.ilean.hash`
- `.lake/build/lib/lean/YulangClosure/PaperExecutionTypingSubstitution.olean`
- `.lake/build/lib/lean/YulangClosure/PaperExecutionTypingSubstitution.olean.hash`
- `.lake/build/lib/lean/YulangClosure/PaperExecutionTypingSubstitution.trace`
- `.lake/build/lib/lean/YulangClosure/PaperTermSubstitution.ilean`
- `.lake/build/lib/lean/YulangClosure/PaperTermSubstitution.ilean.hash`
- `.lake/build/lib/lean/YulangClosure/PaperTermSubstitution.olean`
- `.lake/build/lib/lean/YulangClosure/PaperTermSubstitution.olean.hash`
- `.lake/build/lib/lean/YulangClosure/PaperTermSubstitution.trace`
- `.lake/build/lib/lean/YulangClosure/PaperTypeBetaExecution.ilean`
- `.lake/build/lib/lean/YulangClosure/PaperTypeBetaExecution.ilean.hash`
- `.lake/build/lib/lean/YulangClosure/PaperTypeBetaExecution.olean`
- `.lake/build/lib/lean/YulangClosure/PaperTypeBetaExecution.olean.hash`
- `.lake/build/lib/lean/YulangClosure/PaperTypeBetaExecution.trace`
- `.lake/build/lib/lean/YulangClosure/PaperTypeFormation.ilean`
- `.lake/build/lib/lean/YulangClosure/PaperTypeFormation.ilean.hash`
- `.lake/build/lib/lean/YulangClosure/PaperTypeFormation.olean`
- `.lake/build/lib/lean/YulangClosure/PaperTypeFormation.olean.hash`
- `.lake/build/lib/lean/YulangClosure/PaperTypeFormation.trace`
- `.lake/build/lib/lean/YulangClosure/PaperTypeSubstitution.ilean`
- `.lake/build/lib/lean/YulangClosure/PaperTypeSubstitution.ilean.hash`
- `.lake/build/lib/lean/YulangClosure/PaperTypeSubstitution.olean`
- `.lake/build/lib/lean/YulangClosure/PaperTypeSubstitution.olean.hash`
- `.lake/build/lib/lean/YulangClosure/PaperTypeSubstitution.trace`
