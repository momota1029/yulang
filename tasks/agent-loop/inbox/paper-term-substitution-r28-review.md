# R28 independent M1 review — r1

Assignment: R28 independent M1, `FULL-PAPER-TYPE-SUBSTITUTION-20261026/r28`, contract r1. Reviewer: `/root/r28_independent_m1`; primary launch acknowledgment received before any repository read. Actual model/effort: UNKNOWN; session identifier: UNKNOWN. No authorship of the reviewed artifact, repair contribution, descendants, or reviewer appointments.

**Result: no blocking finding for the fixed represented-judgment intermediate claim.** Recommend primary acceptance at that scope. This review supplies independent source inspection; primary adjudication, integration and all wider parent gates remain separate.

## Frozen evidence and governing source

Baseline supplied by primary: `c0fe13db1f705eb71e7eb440ba6f31458ca90b51` (not independently queried through Git).

| Artifact | Independently observed SHA-256 |
| --- | --- |
| Contract `tasks/agent-loop/sprints/paper-term-substitution-r28-r1.md` | `f3f01a44068bfdde16b3c0116a0aaa010babb8da6a057be3218b19431a33590a` |
| `notes/theory/lean/YulangClosure/PaperTermSubstitution.lean` | `a4f87f9604c03beefdc44de5d45fcd9f5924ca9580c75edf353cf267e69a0d4f` |
| Worker handoff `tasks/agent-loop/inbox/paper-term-substitution-r28.md` | `21c6a4c63e90fe60f1d8b2506a41797386d0f2c876c9aae9316f4a072f2b8d74` |
| Primary log `tasks/agent-loop/inbox/paper-term-substitution-r28-primary-verification.txt` | `533aeba23b130419cbd0f2807b44e1ac1ae9b7a17a2ff357ad38005d522d0933` |
| Manuscript `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| Isolated R27 `PaperExecutionGraphWeakening.lean` | `b0ff39ad89fcb83559cca3147ae55fa7e7f6c31c1b130ec9cd7608e33d1f696e` |

Read root AGENTS.md and AGENTS.pre-sprint.md, goal-driven sprint rules, current state/README, the fixed packet, Lean skill plus sources/execution references, and relevant authority/budget instructions. Read manuscript :953–977, :980–994, its opening 2026-10-23 source-owner correction, and actual raw syntax and six mutual judgment definitions at `PaperExecutionSyntax.lean:39–140, :633–832`. The manuscript remains a research construction; its original all-13-expression/all-11-pattern scope and source-owner correction are preserved as open parent scope.

Independently hash-checked all seven named paper source dependencies against the contract; every hash matches. In contract order: Syntax `e38cd059…`, BinderLaws `568a9a5a…`, TypingSubstitution `3b1588bf…`, TypeFormation `29c1a85b…`, TypeSubstitution `02834720…`, DeclSubst `f1463d4d…`, isolated R27 `b0ff39ad…`. Read pin/config/manifest: Lean 4.35.0; library YulangClosure; no external packages; project `-j1 -M1024`. No toolchain was executed by this reviewer.

## Independent semantic checks

All names below have prefix `YulangClosure.PaperTypes.`.

1. **Actual rejection.** `supportedTermValue` and `supportedTermComputation` inspect source syntax recursively, including list/record children. Their wildcard branches return false for every omitted raw constructor. The four public `termSubstitute*` functions return `none` on a false check. The exact `termSubstituteValue_isSome` and `termSubstituteComputation_isSome` equations agree with these definitions. This is an executable syntax check independent of a typing proposition. Total `replaceTerm*` auxiliaries have unchanged unsupported fallbacks, but unsupported source input cannot reach those fallbacks through the public operation.
2. **Simultaneous order.** A variable returns `rho n` once; the operation does not recurse into that selected replacement. `swapFormalReplacements` swaps indices 0/1, whereas the displayed sequential substitutions collapse both to index 0. `graphFormalReplacements` consumes its head at index 0 and consumes the tail at successor indices, with the tail vector indexed after all formals. The graph-order theorem distinguishes references 10/20 from reversed order.
3. **Every represented term binder.** `liftTermSubstitution` fixes bound index 0 and renames free replacement variables by successor. `renameTermValue` itself lifts renaming beneath binders, protecting bound variables inside replacements. Lambda in both modes, let body, each wrap adapter, continuation body and both union branches lift once; split lifts `binders.length` times. `TermSubstitutionTyped.liftN` uses the actual `extendTupleEnvironment types e = types.reverse ++ e`; the split arity equality connects the syntactic and typing binder counts. The lambda/continuation and two-binder split discriminators express the expected capture avoidance.
4. **Shared forall shift.** At a type abstraction the replacement vector becomes `shiftTermSubstitution rho`, mapping replacement values through `mapPaperValue shiftTypeSubstitution`. `TermSubstitutionTyped.typeShift` applies the existing actual `PaperValueTyped.subst_explicit` theorem to shift D, Xi, source Gamma and target Gamma together. The induction branch uses precisely that instance. Nested type binders in replacement values are protected by `mapPaperValue`'s `liftSub`; term binders remain separately handled. This matches the represented forall rule's shared contexts.
5. **Common intersection witness.** The `both` branch reapplies both induction hypotheses to the identical `target` and `rho`, yielding the same deterministic `replaceTermValue rho value` in both premises. No separately chosen witnesses are introduced. Record labels, raw presence tags, requiredness checks, uniqueness and payload order are retained.
6. **Six complete result indices.** Each `.termSubstitute` is universally quantified over arbitrary D, Xi, source/target environments and vector. Its explicit premise is `TermSubstitutionTyped D Xi source target rho`, meaning every successful source lookup supplies the corresponding typed target replacement. Its other premise is the original exact judgment. Its conclusion supplies an actual `some result` equation and the same judgment at target Gamma with the same D, Xi and result indices: value A; ordered ValuesTyped list As; ValuesAllTyped A; RecordPayloadsTyped record A; computation A; continuation response A and normal result B. This premise is used constructively; no concrete vector instance is inferred from its definition.
7. **R27 application.** Each of the six `.substituteFreshGraphFormals` bodies calls its own original judgment's R27 `.graphWeaken`, then `.termSubstitute`. `graphFormalReplacements_typed` constructs reference typing from the explicit new-graph lookup premise and transports all old tail replacements using R27. The formal source environment is exactly `formals.map Prod.snd ++ source`. `freshGraphReference_application` additionally derives old-lookup preservation from actual `GraphLookupPreserved.freshCons fresh` for one concrete fresh cons extension. Its reference lookup is proved directly. No allocated value, heap or cycle property is inferred from a lookup.

## All 46 declaration types and axiom lines

I read the source statements/proof bodies and compared all 46 public theorem declarations with the primary log's complete printed types. A read-only Python inventory comparison found 46 source names and 46 audit blocks, no missing or extra names. Manual comparison found no changed quantifier, extra hypothesis, lost judgment index or mismatch with the source statement. The inventory comparison is text analysis, not a Lean check or test.

Exhaustive coverage, with the namespace prefix above:

- `TermRenamingTyped.lift`, `.liftN`, `.typeShift`; `PaperValueTyped.termRename`.
- `TermSubstitutionTyped.lift`, `.liftN`, `.typeShift`.
- `.termReplace` on `PaperValueTyped`, `ValuesTyped`, `ValuesAllTyped`, `RecordPayloadsTyped`, `PaperComputationTyped`, `PaperContinuationTyped`.
- `.termSupported` on those same six exact judgments.
- `.termSubstitute` on those same six exact judgments.
- `termSubstituteValue_success`, `termSubstituteValue_failure`, `unsupported_raw_falsifier`, `capture_avoiding_binder`, `simultaneous_order_falsifier`, `forall_replacement_shift`.
- `TermSubstitutionTyped.compose`, `.graphWeaken`; `graphFormalReplacements_typed`.
- `.substituteFreshGraphFormals` on those same six exact judgments.
- `freshGraphReference_application`, `graph_formal_order_falsifier`, `termSubstituteValue_isSome`, `termSubstituteComputation_isSome`, `tuple_pattern_binder_capture`, `sequential_substitution_falsifier`.

The first three `TermRenamingTyped` theorems have printed axiom result `[propext]`. Every other one of these 43 public theorems has `[propext, Quot.sound]`. All 46 axiom lines were inspected; none lists Classical.choice, sorryAx or a project/extra axiom. These are observations of the frozen primary verification output, independently compared with source, not a reviewer rerun. `TermSubstitutionTyped.compose` proves typing of the composed replacement vector; it does not state a general raw substitution-composition equality. The handoff accurately states this boundary.

## Checker evidence, failures and integration boundary

Reviewer Lean/Lake/helper invocations: **0**. Reviewer cache/generated-output reads or writes: **0**. No tests, Git, network, installation, dependency change or nested CLI.

The frozen primary log records native Lake `5.0.0-src+eb6cafb`, Lean `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; preflight elapsed values UNKNOWN. Primary invocation 3, `lake build +YulangClosure.PaperTermSubstitution`, exits 0 in 0.835073168 s; invocation 4, `lake env lean -j1 -M1024 .lake/R28Audit.lean`, exits 0 in 6.126841972 s. Existing unused-variable/simp warnings remain visible. This review does not verify live process or cache ownership from a log.

Worker log retains both material build failures: invocation 3 exit 1 (unknown List.reverseRecOn, goals/map/continuation issues), invocation 4 exit 1 (reserved prefix identifier, forall/support issues). Subsequent builds/audits 5–8 exit 0. I inspected their error/exit locators without altering them. Source scan over the new module and seven named source dependencies for `sorry|admit|axiom|skipKernelTC|native_decide|unsafe` has no matches (rg exit 1); this text scan is separate from printed dependency audits.

A source read at the main checkout's `notes/theory/lean/YulangClosure/PaperExecutionGraphWeakening.lean` failed with “No such file or directory” (sed exit 2). The contract explicitly keeps R27 isolated; I subsequently read its exact matching source at `/tmp/yulang-r28-term-substitution/notes/theory/lean/YulangClosure/PaperExecutionGraphWeakening.lean`, outside every cache path. Thus current main-source module placement is an integration prerequisite owned by primary. Copying R28 alone does not supply its R27 import. No integration edit or fresh build is authorized to this reviewer.

## Scope and parent application

Represented cases are exactly the six original partial judgments: variables/references/literals, tuples/sequences/records, delay and both lambda modes, wrappers, unions/intersection/views, explicit continuation, forall/type application/roll, and the represented computation rules including split, field/lookup, operations/request/resume, template invocation and fail.

Source rejection is a property of the operation's input. Arbitrary untyped vectors are not validated: for example selecting an unsupported variant as `rho 0` at a supported input `variable 0` returns that variant inside `some`. The preservation results explicitly require typed replacements; the represented relation has no variant typing constructor. No output-support guarantee for an arbitrary untyped vector is claimed. Similarly the general graph-formal theorems use hp/hr lookup premises and do not themselves prove freshness of an arbitrary list; the concrete fresh-cons theorem supplies its stated singleton freshness.

Applying the graph-formal results to the manuscript's graph-extension proof discharges its represented derivation-substitution step once the exact reference lookups, source derivations and de Bruijn order are supplied. The first remaining premise is `R27-HEAP-ALLOCATION-1`: construct well-typed heap allocation for all original recursive right-hand sides/body, translate ordered source formals to the exact de Bruijn context, and prove guarded cycles are preserved. Owner: Luna/full-paper recursive-allocation and source-correspondence intake.

Omitted full-paper cases remain variants/nominals, handlers/mappers and their administrative forms, recursive allocation/environments, primitive and full pattern judgments, and registered template-body typing. Full simultaneous term/type/name substitution, owner/operation correspondence, heap typing, guardedness, execution safety, original A/B, inference/executor, source/native and production remain OPEN. No compiler constraints/propagation/consumer/native correspondence is established here.

## Writes and resource cessation

Sole changed path: this report. No scratch file or generated output. All reviewed source bytes remain frozen; only the primary can adjudicate/integrate. Review bound: 300 active seconds, zero checker allowance. First-read clock: 2026-10-25 17:38:27 UTC. The final-close timestamp is below; acknowledgment-to-first-clock overhead was not instrumented, so conservatively charge the full 300-second review allowance with no continuation grant. No children or retained asynchronous process.

After this file is closed, reviewer writes are STOPPED and the report is frozen revision 1. The subsequent receipt supplies its byte hash and actual close timestamp; no further edit or checker/cache action follows.

Final close timestamp (UTC): `2026-10-25T17:41:32.482254+00:00`.
