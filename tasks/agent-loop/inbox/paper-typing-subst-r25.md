# R25 FAILED_CHECK checkpoint — frozen handoff revision 1

Sprint `FULL-PAPER-TYPE-SUBSTITUTION-20261026/r25`, contract r4 SHA-256 `808a4fee292cb6af1aac68dde7bf750c22d6d0a4adb850eb15a2f44a3dac658c`; baseline `70c3d29f76fa54f209fe8271e2ca25f079f26acf`; isolated worktree `/tmp/yulang-r25-mapop`. Admission acknowledgement6b74f92a8 and actual launch receipt preceded source work, edits and checking. All9 frozen inputs matched before writing. The7 inputs outside the2 leased revised sources were rechecked unchanged at freeze, including accepted R24 module.

Actual worker/sole author `/root/r17_forall`; fresh runtime exposed shared CODEX_SESSION_ID01a172ef-fec1-72e3-bd47-bc4d7f51d6aa and CODEX_THREAD_ID01a1736a-fc42-7ab1-bc93-ddab8b55fa6d. Requested registered lean_prover/role-default effort; observed model/effort UNKNOWN. No descendants or contributing authors.

Disposition: FAILED_CHECK under the packet's first-failure stop rule. No repair/retry/audit/primary verification followed the failed build. Source is preserved exactly as it stood at that failure. This is a construction/inference mismatch, not a source-qualified counterexample or a completed theorem. The original parent, R23/R18 and all other OPEN gates remain OPEN.

## Original claim and source gate

Parent: manuscript `docs/yulang-operational-type-safety-ja.tex:953–977`, full-paper simultaneous type substitution and later original inference/executor/A-B over unchanged source scope. Source hash a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b. Source gate was audited and reported PASS before edits:694–719 supplies exact same-operation mapper code/signatures;1024 explicitly preserves normal result type;1109 composes same-mapper payload/response code via substitution/let. Accepted R24 adjudication is the bounded separate-adapter prerequisite, not complete computation typing. Body/adapter D/Xi/Gamma are shared, with only adapter input consed.

## Exact constructed surface and failure

Changed leased source paths:
1. PaperExecutionSyntax.lean adds `YulangClosure.PaperTypes.PaperComputationTyped.mapOperation` with original body resultType, one unique operation declaration, both exact witness arities/full instance equalities, and both R24 adapter derivations under the same captured contexts. Lower imports do not reference R24.
2. PaperExecutionTypingSubstitution.lean adds the corresponding common arbitrary-σ recursor branch. The six public transport statements and all previous case text were left in place; this extended proof does NOT compile.
3. New PaperMapOperationIntegration.lean imports revised TypingSubstitution and accepted R24 evidence and constructs `PaperComputationTyped.mapOperationInversion` and `PaperComputationTyped.mapOperation_iff` with exactly body typing at unchanged resultType AND MapperPlanTyped at the same D/Xi/Gamma. These upper declarations were not reached by a successful build and are unchecked.

Actual first failed diagnostic, retained unabridged in the worker-checks log:
```text
error: YulangClosure/PaperExecutionTypingSubstitution.lean:471:12: Application type mismatch: The argument
  sourceEq'
has type
  OperationInstance.subst σ source =
    (OperationDeclaration.substAmbient σ declaration).instantiate (mapOperationArguments σ sourceArguments)
but is expected to have type
  source = (OperationDeclaration.substAmbient σ declaration).instantiate (mapOperationArguments σ sourceArguments)
in the application
  PaperComputationTyped.mapOperation (ihBody σ) resolved' sourceArity' targetArity' sourceEq'
Some required targets logged failures:
- YulangClosure.PaperExecutionTypingSubstitution
error: build failed
```

The precise remaining construction premise is to instantiate the new mapOperation constructor with the mapped source/target instances while consuming mapped resolution/instance equalities, and then actually check the complete branch/inversion/iff/R24 dependency cone. The constructor application currently inferred the old source, so the full mapped source equality cannot be consumed. Explicit mapped source/target arguments are a plausible next repair to assess, not an executed repair or proof. Owner: primary proof intake/adjudication under an explicit continuation/new packet; the stopped worker has no authority to change these frozen bytes or rerun a checker.

No new conclusion can yet be applied to the parent: the common six-judgment substitution proof fails for this extended relation, and the upper iff/inversion are not kernel-accepted. R24 source is byte-unchanged but must be rechecked against any successfully revised computation judgment before integration. No earlier green receipt is reused as proof of the new dependency cone. No concrete execution/frame/continuation/resumption/freshening/term-substitution/source-native claim was attempted.

## Actual checker receipts

Sole native executable `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`; cwd `/tmp/yulang-r25-mapop/notes/theory/lean`; LEAN_NUM_THREADS=1; project moreLeanArgs=-j1 -M1024. No Lean flags were passed as Lake build options.

- Literal invocation1: `lake --version`, exit0,0.038396735s. Actual output: Lake5.0.0-src+eb6cafb, Lean4.35.0.
- Literal invocation2: `lake env lean -j1 -M1024 --version`, exit0,0.072460844s. Actual Lean4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release.
- Literal invocation3: `lake build +YulangClosure.PaperMapOperationIntegration`, exit1,20.574106925s. Full output, including dependency warnings, completion lines and the complete failure, is retained in exact leased `tasks/agent-loop/inbox/paper-typing-subst-r25-worker-checks.txt`.

AUDIT NOT_RUN. `.lake/R25Audit.lean` was never created. No theorem type/axiom output or bundled validator PASS exists for R25. No kernel acceptance, independent review, parent closure or production readiness is claimed. The failed source must not be represented as proved even though no source hole was intentionally inserted.

## Resources, remaining gates and cessation

3 literal serial invocations consumed,20.684964504 checker/process-wall seconds. Worker budget7 of10 and total9 of12 invocations are numerically unspent, with159.315035496 seconds below the180-second checker ceiling; they are NOT permission to continue after the mandatory failure stop. Primary has explicitly forbidden further checking in this failed checkpoint, including final verification. No budget reset/transfer. Active model time uninstrumented; no invented duration; original1800-active-second shared envelope retained.

No tests, default/full build, Rust/compiler work, network/dependencies/global-default change, root import, contract/current/status/index/reviewer/Git mutation, external contact or children. Accepted R24 and all other read-only dependencies remain unchanged. The dedicated leased `.lake/build` contains partial products of the failed focused build; these are left untouched, not cleaned or promoted. No primary-only verification log was written.

Remaining original gates include one-step mapOperation/request/frame/continuation composition, response plugging/freshening, term substitution, R23-TEMPLATE-CALLER-CONTEXT-EMBEDDING-1, R18 variant correspondence, full paper typing/substitution, inference/executor, A/B, source/native/Rust and production. NO_SAFE_CODE_SLICE remains. The source rule was not weakened or narrowed to hide this proof failure.

STOPPED: all3 checker subprocesses returned (exits0,0,1); their tool session completed. No active checker/command/subprocess session or descendant remains. After this final handoff write, all source/handoff/log/cache writes STOPPED. Source was not repaired after failure. Sole cache ownership may transfer to primary only upon this actual cessation receipt, for adjudication/preservation without checker reruns. No commit was made by this worker.

Frozen changed-path/log SHA-256:
- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`: `eec31d92375ea700061ff6b0a8c5ac7742db5fe77aa96dd28bc75ad7c93fc2dd`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`: `6e8c1b8d1cf62736d6df172430bf20e44d35b6d527d468b07dc80ebe7ce736f3`
- `notes/theory/lean/YulangClosure/PaperMapOperationIntegration.lean`: `98e78766e2d2671d6d4aae6250fbe001c3eb8e9825df1aac62e5c97efcf1851f`
- `tasks/agent-loop/inbox/paper-typing-subst-r25-worker-checks.txt`: `0da3d9820e2d635b7ab7fe7dbfb076491dfeabcc9ac7829da636ff7292a52a92`

Frozen input hashes at admission:
- `docs/yulang-operational-type-safety-ja.tex`: `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`
- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`: `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`: `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41`
- `notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean`: `568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a`
- `notes/theory/lean/YulangClosure/PaperOperationMapperTyping.lean`: `175c307e00bea7ba6ec44ff153f50a7d9d943de8bdc3d4dccb02a41bc53dde77`
- `notes/theory/lean/YulangClosure/PaperTypeFormation.lean`: `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`
- `notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean`: `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861`
- `notes/theory/lean/YulangClosure/DeclSubst.lean`: `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`
- `tasks/agent-loop/inbox/paper-typing-subst-r24-adjudication.md`: `0f8ef9853dfeb07a194b0bb74d4bcb3c9bea667225b1af856a831668ed28e4c5`
