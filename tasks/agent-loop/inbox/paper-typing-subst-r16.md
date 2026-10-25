# R16 handoff — first construction invocation violation

- Sprint/contract: `FULL-PAPER-TYPE-SUBSTITUTION-20261025/r16`, SHA-256 `b445530ce73032a845b2059beb76bbc58bd4248a0b11c45840fab9e1945ca60a`. Assignment/handoff revision: 1.
- Worker: `/root/r16_syntax_proof`; actual task message received from `/root`. Session UUID, observed model and observed effort UNKNOWN. No descendants or third-party contact. Primary owns authority, final checker/cache, independent review and integration.
- Baseline: primary packet names `4d35bba7609319c13766794cfad19fb834363f64`; contract retains historical R15 baseline `71e40c382e8caf2114d8d6819215ab0c8605a428`. Read-only HEAD after primary state work: `6e084962fd98783773b0be4d4dafbe8b3c4e3b25`. No Git mutations by this worker.
- Exact lease: `notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean`, `notes/theory/lean/.lake/R16Audit.lean`, this handoff. Only this handoff was written. Helper source unchanged; audit scratch not created. No cache/generated output was requested from Lean; primary explicitly retained `.lake/build` ownership.

## Source, unchanged claim, and dependencies

Read root `AGENTS.md`, `AGENTS.pre-sprint.md`, `rules/goal-driven-sprints.md`, skill plus `references/sources.md` and `references/execution.md`, current state/navigation, R15 handoff, pinned project files, relevant README, actual syntax/mappers and judgments. Original manuscript: `docs/yulang-operational-type-safety-ja.tex` opening correction notice; type rules at 203–207/237; substitution lemma/proof at 953–977. The correction excludes automatic source-owner correspondence for the old raw-resume behavior. Manuscript status is research/self-checked; no semantic authority or independent review is inferred.

Parent is full paper typing substitution, including value-only forall introduction with freshness over the shared declaration/environment context; all inference/executor and original A/B parents remain OPEN. Current packet requires every depth `n`, substitution `σ`, and raw object `x`, with no hypotheses, to satisfy:

```text
mapFamily (liftSubN n (liftSub σ))
  (mapFamily (liftSubN n shiftTypeSubstitution) x)
= mapFamily (liftSubN n shiftTypeSubstitution)
  (mapFamily (liftSubN n σ) x)
```

Read actual owners `PaperExecutionSyntax.lean:38–542,617–716`, `PaperTypeFormation.liftSubN`, `OperationDeclaration.substAmbient`, and the existing binder helper definitions. All nine raw families remain required: Value, Computation, PatternPlan, ConstructorBranch, GuardedBranch, ValueArm, OperationArm, HandlerPlan, MapperPlan. Also required: actual TemplateBody executable code, OperationDeclaration, NominalConstructor, PrimitiveSignature and DeclarationTable including preserved native-list identity. No accepted constructor, optional field/guard/default, attached list/product, operation instance or shared witness was removed.

Actual `sha256sum` matched these frozen dependencies:

```text
59a4dd5cd4a8056196f3e0d084869099f78039d083b7b47d7e9a1d3e6c0296a0 PaperExecutionBinderLaws.lean
8789ee5a79b93d6fef2cff1db8692de67f4bc8b290a92ec3e37cac34b0074939 PaperExecutionSyntax.lean
02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861 PaperTypeSubstitution.lean
29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13 PaperTypeFormation.lean
f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258 DeclSubst.lean
```

Typing/R15 hashes were read from the fixed packet and R15 receipt, not independently rehashed in this stopped attempt. No dependency was modified. Installed API consulted: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean/Init/Data/List/{Attach,BasicAux,Lemmas}.lean`, for `List.attach_map_val`, `List.sizeOf_lt_of_mem`, `List.map_congr_left` and `List.map_inj_left`.

## Material failure and actual checker evidence

`elan which lake` exited 0 and resolved `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`. Configured pin is `leanprover/lean4:v4.35.0`; observed executable versions UNKNOWN. Primary explicitly instructed skipping version-only calls because each would consume construction budget.

Call 1, cwd `/home/momota1029/rust/yulang/notes/theory/lean`: preparatory Python used path `notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean` while already inside the project. It failed before any write:

```text
Traceback (most recent call last):
  File "<stdin>", line 3, in <module>
  File "/usr/lib/python3.12/pathlib.py", line 1029, in read_text
    with self.open(mode='r', encoding=encoding, errors=errors) as f:
  File "/usr/lib/python3.12/pathlib.py", line 1015, in open
    return io.open(self, mode, buffering, encoding, errors, newline)
FileNotFoundError: [Errno 2] No such file or directory: 'notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean'
```

Because the shell script continued after Python exit 1, this exact command then executed:

```sh
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake env lean -j1 -M1024 YulangClosure/PaperExecutionBinderLaws.lean
```

Shell/checker exit 0; total tool wall time 0.275646137 seconds (Python plus Lean, not isolated checker time). Lean emitted only existing line-67 unused-simp warnings for `liftSubN` and `Nat.add_assoc`. This checked unchanged helpers only. The required common `ShiftAt` strong-induction term and nontrivial syntax case were never written or instantiated. Therefore call 1 violated the fixed first-invocation condition. The worker reported this immediately to the primary and stopped construction; there was no recursor/motive reconnaissance and no second Lean/Lake call.

Resource charge: 1/10 worker construction invocations; 9 unspent construction invocations. Calls 11–12 remain reserved for the primary after writes stop. Overall packet ceiling remains 12 and cannot be reset by this handoff. Active time and isolated checker time were not instrumented. No tests, default-target/Rust build, dependency installation, checker bypass, `sorry`/`admit` or project axiom were introduced.

## Outcome and parent application

Outcome class: failed protocol/construction attempt. No theorem was delivered. No new printed theorem type or `#print axioms` output exists; prior R15 audits are historical evidence only. No strict-decrease case was checked. No raw family or declaration entry law was proved. Kernel acceptance of the unchanged helper is distinct from the missing syntax/declaration obligation, independent review, source/native correspondence and production authority.

Parent application: none. First remaining premise is the unchanged nine-family raw mapping law, followed by executable template/declaration commutation. Owner: primary proof intake. The failure supplies no mathematical counterexample. The planned method remains exactly one common `Nat.strong_induction_on` with nine depth-generalized fields, ordinary constructor cases, genuine strict decreases for children and container projections, depth+1 under Value.typeAbstraction and depth+actual rigidBinders under OperationArm. A primary adjudication is required before any continuation because the mandated first call has already been consumed incorrectly; the worker cannot revise this contract.

No source-to-constraint-to-propagation-to-consumer/native bridge was established. Full forall rule, six-judgment transport, typing, graph guards, executor/inference, original A/B, source/native/Rust and independent review remain OPEN. No commit-ready proof milestone.

Worker state: STOPPED. Writes stopped after this handoff revision 1; no descendants, no outstanding processes or generated-output leases. No further writes or Lean/Lake invocations will occur without an explicit new primary instruction. Frozen handoff SHA-256 is returned in the final message (self-hash excluded).
