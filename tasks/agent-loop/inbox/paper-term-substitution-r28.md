# R28 represented-judgment term substitution — worker handoff r1

Sprint/contract: `FULL-PAPER-TYPE-SUBSTITUTION-20261026/r28`, r1, SHA-256 `f3f01a44068bfdde16b3c0116a0aaa010babb8da6a057be3218b19431a33590a` (contract read from the primary checkout). Assignment: R28-REPRESENTED-TERM-SUBSTITUTION; handoff revision 1. Baseline supplied by primary: `c0fe13db1f705eb71e7eb440ba6f31458ca90b51`; no Git command run by worker. Isolated checkout `/tmp/yulang-r28-term-substitution`.

Role/worker: registered `lean_prover`, `/root/r28_registered_lean_prover`; accepted packet, waited, then began only after primary's explicit launch acknowledgment. Child session identifier UNKNOWN; requested exact model/effort UNKNOWN; observed exact model/effort UNKNOWN. Role/config labels do not establish execution metadata. Sole author this worker; no descendants or outside contributors.

Outcome: **kernel-accepted intermediate candidate, pending primary verification and fresh independent review**. No self-certification, source/native correspondence, full-parent closure, or production authority.

## Original source and preserved claim

Read manuscript `docs/yulang-operational-type-safety-ja.tex:953–977` (term/type/name substitution), `:980–990` (immutable graph extension), the opening 2026-10-23 source-owner correction, and the actual six mutual judgments in `PaperExecutionSyntax.lean`. The manuscript is a research construction, not an approved language specification. Its original scope includes all 13 expressions/11 patterns, shared environments, handlers, recursive allocation and guarded graph cycles; this artifact does not replace that scope by the represented fragment.

For arbitrary `D`, `Xi`, `Gamma`, `Gamma'`, `rho`, every successful source environment lookup `Gamma[n]=A` supplies `PaperValueTyped D Xi Gamma' (rho n) A`. For each of the six original judgments, the operation returns `some result` and preserves `D`, `Xi`, and every result index exactly while replacing only `Gamma` by `Gamma'`. `PaperContinuationTyped` retains separate response/result types; lists retain the same ordered list of types; records retain type, labels, requiredness and raw presence tags. Intersection premises use one identical substituted value, preserving the shared witness.

`TermSubstitutionTyped` is the usual typed-replacement premise, not a concrete instance inferred from a proposition definition. Its lift, type-shift, composition and graph-transport instances are constructed from derivations. No `LocalLaws`, safety-as-typing definition, project axiom, stronger hypothesis or reduced source language is used to claim the full parent.

## Construction and source map

All declarations below are under `YulangClosure.PaperTypes`.

- `renameTermValue`/`renameTermComputation` implement term-variable renaming. `TermRenamingTyped.lift`, `.liftN`, `.typeShift`, and `PaperValueTyped.termRename` prove the environment transport used for capture avoidance.
- `liftTermSubstitution rho 0 = variable 0`; at `n+1` it returns `renameTermValue Nat.succ (rho n)`. `liftTermSubstitutionN` repeats this once per binder; `.liftN` proves the exact existing `extendTupleEnvironment` convention (`types.reverse ++ environment`). Lambda, let, wrap adapters, continuation and each union branch lift once; tuple split lifts by its checked binder arity.
- `shiftTermSubstitution` maps every replacement by `mapPaperValue shiftTypeSubstitution`. `.typeShift` uses existing `PaperValueTyped.subst_explicit` and the same shifted `D/Xi/Gamma/Gamma'` in the forall case. No per-use change of a shared resource type is assumed.
- `replaceTermValue`/`replaceTermComputation` are total implementation auxiliaries. Variables select `rho n` once, without recursively substituting inside that selected replacement. Their unsupported fallback is **not** the partial public operation and carries no unsupported-form success claim.
- `supportedTermValue`/`supportedTermComputation` inspect syntax, independently of typing; each omitted raw constructor returns false, recursively including omitted subterms. Public `termSubstituteValue`, `termSubstituteComputation`, `termSubstituteValues`, `termSubstituteFields` return `none` when this syntax check fails. `termSubstituteValue_isSome` and `termSubstituteComputation_isSome` characterize success exactly by that check. The source guard does not validate arbitrary untyped replacement vectors; the preservation theorems require and use typed replacements.
- Six `.termReplace` results prove typing of the auxiliary traversal; six `.termSupported` results prove represented derivations pass the syntax check; six `.termSubstitute` results combine actual Option success with typing preservation.
- `composeTermSubstitution outer inner n = replaceTermValue outer (inner n)`. `TermSubstitutionTyped.compose` proves this composed simultaneous vector is typed. A general raw syntactic substitution-composition equality is not claimed or delivered.

Decisive discriminators: `capture_avoiding_binder` covers lambda and continuation with free replacement `variable 0`; `tuple_pattern_binder_capture` covers the represented split pattern with two binders; `simultaneous_order_falsifier` swaps two formals; `sequential_substitution_falsifier` proves sequential replacements collapse that pair and that reversed graph-reference order differs; `forall_replacement_shift` exposes the required actual type-shifted replacement; `unsupported_raw_falsifier` rejects variant, nominal, recursive and handler raw inputs. General isSome characterizations also cover every other omitted constructor through the explicit syntax definitions.

## Parent application and first remaining premise

`graphFormalReplacements` takes formals in **de Bruijn order**: the list head replaces index zero, as `graph_formal_order_falsifier` proves for two references. Its source environment is exactly `formals.map Prod.snd ++ source`, not an implicit reversed source-formal list. `graphFormalReplacements_typed` constructs the typed vector from successful new-reference lookups and old tail replacements transported by R27.

Each of the six `.substituteFreshGraphFormals` theorems explicitly applies that judgment's R27 `.graphWeaken`, then the corresponding simultaneous substitution theorem. `freshGraphReference_application` additionally instantiates R27 `GraphLookupPreserved.freshCons` for a concrete fresh graph extension. Thus a represented derivation under formal types yields a represented typed result after replacing formals by fresh references, preserving the complete original judgment indices. This discharges the represented derivation-substitution step used inside manuscript :980–990, conditional on its stated reference lookups and derivations.

First remaining full graph premise: a concrete well-typed heap allocation for all recursive right-hand sides/body, with the original source-formal order translated into the exact de Bruijn environment and with guarded cycles preserved. Owner: Luna/full-paper recursive-allocation and source-correspondence intake (`R27-HEAP-ALLOCATION-1`). The source `recursive` constructor has no represented typing rule and is deliberately rejected here. These proofs do not construct a heap or establish its guards.

Full term/type/name substitution also needs the omitted paper judgment/rule instances: variants/nominals, handlers/mappers, primitive and full pattern judgments, graph allocation/recursive environments, and registered template-body typing. Owner: Luna/full-paper substitution gate. Inference/executor, operation/owner correspondence, original A/B, source/native and production remain OPEN. There is no compiler constraint-generation, propagation, consumer/native bridge in this packet; `NO_SAFE_CODE_SLICE` remains in force.

## Actual checking and failures

Resolved existing native Lake by read-only `elan which lake` from the isolated project: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`. Actual versions: Lake `5.0.0-src+eb6cafb (Lean version 4.35.0)`; Lean `4.35.0`, x86_64 Linux, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release. Read pinned local `Init/Data/List` sources for unavailable list API names.

Every invocation used `LEAN_NUM_THREADS=1`. Focused builds use project `-j1 -M1024`. Commands, exact outputs and failures remain in the leased worker log. No default/full build, tests, network, install/update, dependency/config/root-import edit or Git mutation.

| Invocation | Native Lake arguments | Exit | Seconds |
| --- | --- | --- | --- |
| 1 | `lake --version` | 0 | 0.033104 |
| 2 | `lake env lean --version` | 0 | 0.061319 |
| 3 | `lake build +YulangClosure.PaperTermSubstitution` | 1 | 23.454855 |
| 4 | `lake build +YulangClosure.PaperTermSubstitution` | 1 | 7.627233 |
| 5 | `lake build +YulangClosure.PaperTermSubstitution` | 0 | 4.741019 |
| 6 | `lake env lean -j1 -M1024 .lake/R28Audit.lean` | 0 | 3.121843 |
| 7 | `lake build +YulangClosure.PaperTermSubstitution` | 0 | 7.817236 |
| 8 | `lake env lean -j1 -M1024 .lake/R28Audit.lean` | 0 | 3.449161 |

Build 3 failed on nonexistent `List.reverseRecOn`, list-map simplifications, record attach mapping, and continuation unfolding. Build 4 failed on reserved identifier `prefix`, explicit forall shifted-vector argument, and support/continuation unfolding. Each was repaired from the actual printed goals; no unchanged command retried without changed source. Builds 5 and 7 passed; audits 6 and 8 passed. Existing dependency warnings and local unused-simp/implicit size-proof variable warnings remain; no failure output was replaced.

The skill's `audit_source` generated the leased audit, with its whitelist tightened to `[propext, Quot.sound]`; `validate_audit` passed on all ordered markers, printed complete types and axiom reports. The CLI itself would create an unleased temporary audit directory and repeat version commands, so its functions were used for the exact leased manual commands instead. Final audit covers **all 46 public theorem declarations**, including all six preservation/success results and six graph applications. No theorem-kind or axiom bypass was used.

Complete axiom results: `TermRenamingTyped.lift`, `.liftN`, `.typeShift` depend on `[propext]`. **Every other public theorem listed below depends on `[propext, Quot.sound]`.** None depends on `Classical.choice`, `sorryAx`, project axioms or unsupported axioms. The final source scan for `sorry|admit|axiom|skipKernelTC|native_decide|unsafe` over the new module and seven paper dependencies returned no matches (exit 1). Printed types and complete per-theorem axiom lines are preserved in invocation 8, not inferred from grep.

Audited fully qualified names (prefix `YulangClosure.PaperTypes.`):

- `TermRenamingTyped.lift`
- `TermRenamingTyped.liftN`
- `TermRenamingTyped.typeShift`
- `PaperValueTyped.termRename`
- `TermSubstitutionTyped.lift`
- `TermSubstitutionTyped.liftN`
- `TermSubstitutionTyped.typeShift`
- `PaperValueTyped.termReplace`
- `PaperValueTyped.termSupported`
- `ValuesTyped.termReplace`
- `ValuesAllTyped.termReplace`
- `RecordPayloadsTyped.termReplace`
- `PaperComputationTyped.termReplace`
- `PaperContinuationTyped.termReplace`
- `ValuesTyped.termSupported`
- `ValuesAllTyped.termSupported`
- `RecordPayloadsTyped.termSupported`
- `PaperComputationTyped.termSupported`
- `PaperContinuationTyped.termSupported`
- `PaperValueTyped.termSubstitute`
- `ValuesTyped.termSubstitute`
- `ValuesAllTyped.termSubstitute`
- `RecordPayloadsTyped.termSubstitute`
- `PaperComputationTyped.termSubstitute`
- `PaperContinuationTyped.termSubstitute`
- `termSubstituteValue_success`
- `termSubstituteValue_failure`
- `unsupported_raw_falsifier`
- `capture_avoiding_binder`
- `simultaneous_order_falsifier`
- `forall_replacement_shift`
- `TermSubstitutionTyped.compose`
- `TermSubstitutionTyped.graphWeaken`
- `graphFormalReplacements_typed`
- `PaperValueTyped.substituteFreshGraphFormals`
- `ValuesTyped.substituteFreshGraphFormals`
- `ValuesAllTyped.substituteFreshGraphFormals`
- `RecordPayloadsTyped.substituteFreshGraphFormals`
- `PaperComputationTyped.substituteFreshGraphFormals`
- `PaperContinuationTyped.substituteFreshGraphFormals`
- `freshGraphReference_application`
- `graph_formal_order_falsifier`
- `termSubstituteValue_isSome`
- `termSubstituteComputation_isSome`
- `tuple_pattern_binder_capture`
- `sequential_substitution_falsifier`

## Frozen paths and hashes

Only four new files plus the dedicated cache were written; all paths are relative to the isolated checkout.

- `notes/theory/lean/YulangClosure/PaperTermSubstitution.lean`: `a4f87f9604c03beefdc44de5d45fcd9f5924ca9580c75edf353cf267e69a0d4f`
- `notes/theory/lean/.lake/R28Audit.lean`: `a8db6a7d8b5b1a12ff00110e2f64c8d6ff48e87dca8522a9d4a449914b606f5d`
- `tasks/agent-loop/inbox/paper-term-substitution-r28-worker-checks.txt`: `dbbc1395cb943a83e00f720622e9c15022efb8d2479782866ae426f1663b44b8`
- `notes/theory/lean/.lake/build`: 64 files; SHA-256 of the sorted UTF-8 manifest printed in the worker log: `b068bb4de6f6396a8050033e3a4c55f2b24d6b4432a7b67e8991521f7b396af4`. Each row is `sha256  relative-to-project-path\n`.
- `tasks/agent-loop/inbox/paper-term-substitution-r28.md`: this one revision-1 handoff; its final byte hash is sent in the cessation message.

Direct frozen input hashes, rechecked unchanged after final audit:

- `docs/yulang-operational-type-safety-ja.tex` (original manuscript): `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`
- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean` (six original partial judgments): `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`
- `notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean` (shared binder algebra): `568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean` (existing type transport): `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41`
- `notes/theory/lean/YulangClosure/PaperTypeFormation.lean` (type formation): `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`
- `notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean` (type substitution): `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861`
- `notes/theory/lean/YulangClosure/DeclSubst.lean` (declaration substitution): `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`
- `notes/theory/lean/YulangClosure/PaperExecutionGraphWeakening.lean` (frozen R27): `b0ff39ad89fcb83559cca3147ae55fa7e7f6c31c1b130ec9cd7608e33d1f696e`
- `notes/theory/lean/lean-toolchain` (pin): `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`
- `notes/theory/lean/lakefile.toml` (configuration): `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194`
- `notes/theory/lean/lake-manifest.json` (dependencies): `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`
- `tasks/agent-loop/inbox/paper-execution-graph-weakening-r27-review.md` (R27 independent review): `65cae0d25f01e51e5330946234d105d19761a2d431424048c29689c14603b60a`
- `tasks/agent-loop/inbox/paper-typing-subst-r26-adjudication.md` (R26 failure adjudication only): `6551f28f5da2bfff5905990c98abeac95b19f242b1ad6e27bdf370f27c3c25f1`

## Resource and cessation receipt

Literal Lean/Lake invocations: **8/10**, including both version queries; checker elapsed **50.305770/120 seconds**. Two failed invocations, below the three-failure stop trigger; no timeout. Whole active duration was not instrumented from acknowledgment, so conservatively charge the complete **900-second worker allowance** and spend no further active proof budget. No unused earlier-sprint budget transferred.

Final checker process groups all returned through `communicate`; no running checker, descendant process, or agent was retained. A final process snapshot contained only the snapshot shell/rg itself, no R28 Lean/Lake process. No children were spawned, so descendant agent leases and reservations are empty. All old UNKNOWN reservations remain untouched.

**Writes STOPPED after this revision-1 handoff is closed.** New proof, audit, worker log and build/cache bytes are frozen; no further edits, checker calls or generated output. Exact lease set is exhausted or frozen. Independent review and primary verification have not run on this final artifact; only Luna may allocate them or integrate it. No scheduling/status/index/question/compiler/test/config/dependency or other worker file was written.
