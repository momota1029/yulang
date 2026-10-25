# R50 frozen worker handoff

Sprint-ID: PAPER-EMPTY-OWNER-RESUME-20261026/r50. Assignment: r50_empty_owner_resume_proof. Handoff revision: 1.
Contract: `/home/momota1029/rust/yulang/tasks/agent-loop/sprints/paper-empty-owner-resume-r50-r4.md`, SHA-256 `bf5b219258268282865931a4c9d2778a4e340ee0ad91b6c89397ceb1da1033c7`.
Baseline: `e85eb20fd40426316790d1fb543d64b7676b58e8`, provisioned by primary in isolated `/tmp/yulang-r50-empty-owner-resume`.
Author/actual worker: `/root/r50_empty_owner_resume_proof`, registered `lean_prover`; session `01a172ef-fec1-72e3-bd47-bc4d7f51d6aa`. Requested role defaults; observed model/effort UNKNOWN. No coauthors or descendants.
Outcome class: candidate, kernel accepted for the bounded existing paper judgments; independent review NOT_RUN by this worker. Production authority unchanged.

## Original claim and corrections

`docs/yulang-operational-type-safety-ja.tex` §複数回 resume と metadata :458–466 and handler/resume local preservation :1069–1085: `K : Kont(Q,A), v : Q ⟹ Resume(K,v) : A`, allowing repeated uses of unchanged saved code. Manuscript SHA-256 `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
The opening correction notice :57–64 and `docs/yulang-source-type-safety-ja.tex` :390–449 separate executable owners from immutable historical evidence; nonempty-owner freshening must respect that correction. `notes/theory/2026-10-24-corrected-core-value-continuation.md` §§1–2,4–7 was consulted as a research draft, not semantic authority or proof evidence.
This packet discharges only the expressly leased outer empty-owner case, where freshening has no owners to rename. No fresh-renaming law, source simulation or LocalLaws parameter is assumed.

## Frozen artifacts and writes

All paths below are relative to the isolated checkout. No main-checkout files were written.

| Artifact | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/PaperResumeExecution.lean` | `5ab59033b0cea347144c50a5323e4dd6cb59cc6bfbdc0bffd063a4808e741935` |
| `notes/theory/lean/.lake/R50Audit.lean` | `7cc577fff482bac2674c6449b43cf89edfb04c9bc258c6bfaf3e5bed499aea3e` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/PaperResumeExecution.olean` | `64efbe5a2ffc700405e55906201bdb72b8414e1c7913440eeb049022c23ed1b5` |
| `tasks/agent-loop/inbox/paper-resume-execution-r50-worker.log` | `4a99134be26e0924d8c0337f525a6b11723fde415c2d0db101e9913b43ed73ea` |

Other writes: dedicated `notes/theory/lean/.lake/build` subtree (104 files, 28212739 bytes), call-01/02/03/04 `.stdout` and `.stderr`, this handoff. Cache manifest SHA-256 `2e82c787fe2156cdcb0b4882e7bb8702e1066780b66083ad0d13e6888a65dcfe`. No `.lake/config` or `R50DependencyCheck.lean` was created. Calls 05–08 were unused. All existing source modules, root imports, manifests/toolchain, rules, questions, central records, Rust and Git stayed untouched.

All eleven frozen pins were checked before writes, after contract-path reconciliation and after checking; every pin matches. Exact pin map and all 13 transitive project import hashes are preserved in `paper-resume-execution-r50-worker.log` under `POST_WORK_PINS` / `PROJECT_DEPENDENCY_CONE_HASHES`.

## Checked interface and parent application

The namespace is `YulangClosure.PaperTypes.PaperResumeExecution`. `resumeStep` matches only `.resume (.continuation [] binder body) response` and calls existing R28 `termSubstituteComputation (PaperCoreStep.singleReplacement response) body`. Index zero becomes the response; successor indices refer to the unchanged outer environment, with the existing binder lifting under nested terms/types.
`resume_applicable` and `resume_preservation` quantify over arbitrary shared `d`, `g`, `e`, binder, body, response and separate `q`, `a`, requiring only the original `PaperContinuationTyped ... q a` and `PaperValueTyped ... response q`. `typed_resume_preservation` also consumes the original computation typing rule directly. No conclusion was moved into a new premise.

`perform_through_stack_resumable` directly applies `YulangClosure.PaperTypes.PaperPerformLetExecution.perform_through_stack`, retaining its same operation instance, payload, contexts, finite ordinary-let stack and one existential `saved` body. It retains the original perform equation, request trace and typed final request, then proves every correctly typed response resumes to the final result type. `perform_through_stack_two_resumes` applies the same accepted theorem once and resumes that identical `saved` body independently for both arbitrary responses. `two_resumes` retains the unchanged original continuation typing derivation in its conclusion. Reapplication requires no consumption/single-use premise.

`resume_prefix` uses literal existing R49 `Trace` and `trace_preservation` after response substitution, retaining arbitrary pending typed stack and final result type. It proves final `StateTyped`, typed erased final computation, and an `ErasureTrace` from the pre-resume plugged computation. `ComputationStep` embeds every old R49 `PaperLetContextStep` and adds only empty-owner resume under finite ordinary lets; `trace_erasure` consumes actual R49 `erasure`. Administrative equalities are explicit evidence, not invented steps. This proves every supplied finite prefix; it does not assert termination, general progress or a whole executor.

Discriminators prove response/outer de Bruijn index behavior, noncapture through a let binder, rejection of a nonempty outer owner list by this partial operator, and concrete `Q=int`, `A=bool` preservation in arbitrary contexts.

For the bounded R50 parent there is no remaining mathematical premise beyond the original typing/operation-resolution/arity inputs and the supplied finite Trace. The next acceptance obligations are primary default-root verification and fresh independent review. For the original unrestricted manuscript parent, the first remaining proof obligation is corrected nonempty-owner freshening/capture preservation, owned by Luna's future owner/lifetime proof packet. The source-to-native template/activation/metadata bridge remains separately OPEN at the primary/native correspondence owner.

## Execution and audit evidence

Installed native executable: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`, resolved by read-only `elan which lake` (exit 0). Lake reports `Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)`. Lean reports `Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`.
All four commands ran in `/tmp/yulang-r50-empty-owner-resume/notes/theory/lean` with `LEAN_NUM_THREADS=1`; each process group was bounded to 60 seconds. Exact commands, monotonic start/duration, exits and complete raw output hashes are in the worker log.

| Call | Exact command | Exit | Monotonic seconds |
| --- | --- | --- | --- |
| 01 | `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --version` | 0 | 0.038670524 |
| 02 | `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake env lean --version` | 0 | 0.066202103 |
| 03 | `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake build +YulangClosure.PaperResumeExecution` | 0 | 34.408648903 |
| 04 | `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake env lean -j1 -M1024 .lake/R50Audit.lean` | 0 | 2.263402532 |

Call03 built the selected module and dependency cone (14 jobs), not the default root. Candidate emitted no warnings; inherited linter/deprecation warnings are retained in complete raw stdout. No construction build failure, audit failure or timeout occurred. The briefly missing isolated checkout and r2 filename mismatch were returned to the primary before construction; the primary supplied the checkout and explicit exact-r2-path resume. Those preconstruction read-only failures consumed no Lean/Lake call and were not mathematical counterexamples.

Audit source uses the skill's unmodified `audit_source` generator structure with the contract's exact strict whitelist `{propext, Quot.sound}` in the leased audit, followed by the unmodified `validate_audit` and an additional strict set check. It verifies theorem declaration kind, printed complete `#check @...` types, ordered unique BEGIN/END markers and complete `#print axioms` results. All 18/18 public handwritten theorems passed; each actual axiom list is exactly `[propext, Quot.sound]`. No `Classical.choice`, project axiom or unchecked native evaluation appears. All 13 project source modules in the import cone were scanned with zero `sorry`/`admit`/`axiom`/`debug.skipKernelTC`/`native_decide` matches.

Complete printed types/markers/axiom output: [call04 stdout](paper-resume-execution-r50-call-04.stdout). Exact audit source: [R50Audit.lean](../../../notes/theory/lean/.lake/R50Audit.lean).

| Fully qualified theorem | Actual complete axiom list |
| --- | --- |
| `YulangClosure.PaperTypes.PaperResumeExecution.resumeStep_eq` | `[propext, Quot.sound]` |
| `YulangClosure.PaperTypes.PaperResumeExecution.resume_applicable` | `[propext, Quot.sound]` |
| `YulangClosure.PaperTypes.PaperResumeExecution.resume_preservation` | `[propext, Quot.sound]` |
| `YulangClosure.PaperTypes.PaperResumeExecution.resume_typed` | `[propext, Quot.sound]` |
| `YulangClosure.PaperTypes.PaperResumeExecution.typed_resume_preservation` | `[propext, Quot.sound]` |
| `YulangClosure.PaperTypes.PaperResumeExecution.two_resumes` | `[propext, Quot.sound]` |
| `YulangClosure.PaperTypes.PaperResumeExecution.request_continuation_typed` | `[propext, Quot.sound]` |
| `YulangClosure.PaperTypes.PaperResumeExecution.perform_through_stack_resumable` | `[propext, Quot.sound]` |
| `YulangClosure.PaperTypes.PaperResumeExecution.perform_through_stack_two_resumes` | `[propext, Quot.sound]` |
| `YulangClosure.PaperTypes.PaperResumeExecution.plug_step` | `[propext, Quot.sound]` |
| `YulangClosure.PaperTypes.PaperResumeExecution.resume_erasure` | `[propext, Quot.sound]` |
| `YulangClosure.PaperTypes.PaperResumeExecution.erasureTrace_trans` | `[propext, Quot.sound]` |
| `YulangClosure.PaperTypes.PaperResumeExecution.trace_erasure` | `[propext, Quot.sound]` |
| `YulangClosure.PaperTypes.PaperResumeExecution.resume_prefix` | `[propext, Quot.sound]` |
| `YulangClosure.PaperTypes.PaperResumeExecution.nonempty_owner_rejected` | `[propext, Quot.sound]` |
| `YulangClosure.PaperTypes.PaperResumeExecution.response_outer_discriminator` | `[propext, Quot.sound]` |
| `YulangClosure.PaperTypes.PaperResumeExecution.binder_capture_discriminator` | `[propext, Quot.sound]` |
| `YulangClosure.PaperTypes.PaperResumeExecution.distinct_response_result` | `[propext, Quot.sound]` |

Raw stdout SHA-256:

| Call | SHA-256 |
| --- | --- |
| 01 | `165f92ed239a8c7db772bf5ee9d58c59357b489951582a12c86dc9d8e06b23a2` |
| 02 | `eb22144228dd41cd51a0c84af4f976cd0cef473102dcf99b60be756b11f2b95a` |
| 03 | `f13d0daef86067b9ec805f0e9398eef896beefea8f00228cee7f58e75f1614c0` |
| 04 | `8753fae9e2b966c87ed163f4f2faac7b1049c776b479155ff7c6673080497df6` |

All four stderr files are empty, each SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## Represented cases and open boundaries

The theorems cover all existing `PaperContinuationTyped` / `PaperValueTyped` / `PaperComputationTyped` derivations for the specified empty outer owner list, with no extra body-language restriction. R28 already represents variable/reference/literal, tuple/sequence/record, delay/both entry lambdas/wrap, union/intersection/Top/View, type abstraction/application, roll, continuation, and Ret/let/Force/Call/Resume/split/unioncase/field/lookup/perform/template/request/Fail cases. Nested binders use its existing term/type shifting. No extra condition excludes nested typed continuations.
Raw omitted forms such as nominal/variant, recursive allocation, handlers and other unsupported constructors remain outside those existing typing/substitution judgments; the new module neither adds their semantics nor relabels this as full-paper closure. Outer nonempty owner lists, owner/evidence freshening, handlers/deep handlers, current port/residual graph, graph growth, full-state/source/native simulation, inference A/B, effects and production closure remain open.

`NO_SAFE_CODE_SLICE`: inspected `runtime/machine.rs` saved continuation/ResumeArgument/template entry and `runtime/continuation.rs` immutable TemplateNode storage under `tools/inference-playground/src`. Native Owner/ForwardHandler/View/template/activation and response validation behavior is not modeled by paper-body substitution. No Rust or runtime tests were written/run and no source/native claim is made.

## Resources, next owner and stop

Spent: 4/8 literal calls, 36.776924062/120 checker seconds; remaining 4 calls and 83.223075938 seconds are unused and not permission for extra work. Each call <60 seconds. Measured interval from first logged version-call start to evidence freeze: 402.472897 seconds; startup read-only preparation before that monotonic point was not instrumented. No reset is claimed; primary retains launch/sprint active-time accounting against 1200 active seconds.

Primary TODO R50-ACCEPT-1: preserve these bytes; verify default root and this complete strict audit in `/tmp/yulang-r50-empty-owner-primary`, assign the fresh compiler_referee, and integrate only after its CLEAN result. Proposed root delta is exactly `import YulangClosure.PaperResumeExecution`, solely on Luna's root-import lease. No such edit was made here. Falsifiers: differing pins/bytes, missing audited theorem/type/marker, nonwhitelisted axiom, source scope mismatch, response/result conflation, different saved witnesses, erased-step mismatch or blocking review finding.

Worker state: STOPPED at this frozen revision. All four subprocesses returned; a `/proc` observation found no Lean/Lake process with cwd under this isolated checkout. No descendants or unresolved child leases. Source/audit/log/cache/handoff writes stop after this file is created. No further checker call, Git operation or background process will run. Fresh independent review, primary validation, integration and production status are not self-certified.
