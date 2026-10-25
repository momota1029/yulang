# R47 proof repair failure handoff (revision 1)

Status: FAILED / STOPPED after mandatory strict-audit failure. The final module built successfully, but the strict audit exited 1. No source, audit or checker repairs were attempted after that stop. R46 remains FAILED; R45 remains unchanged. Independent review and primary integration: NOT_RUN.

## Contract and authority

- Sprint: PAPER-PERFORM-LET-REPAIR-20261026/r47; contract SHA-256 `cef97b369ef37114333cb15ff51adf734ef30bcb7e804dbf1cba3c0ec7432630`.
- Fixed detached baseline: `d0d57a893faccde663d32c50f0416b8c244c726c`.
- Actual worker: `/root/r47_perform_let_repair`, registered lean_prover; no descendants. Requested registered role defaults; effective model/effort UNKNOWN.
- Governing reads: AGENTS.md, AGENTS.pre-sprint.md, rules/goal-driven-sprints.md, rules/design-authority.md, current/README navigation, Lean skill and sources/execution references, pinned project README/toolchain/manifests, R46 original failed handoff/candidate/audit.
- Manuscript SHA `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`: opening source-owner correction :54–63; perform :318–319; request-bind and normal-result distinction :340–359; frame plugging :1012–1026; original full-state/current-port/residual-graph parent :1860–1877. The original parent remains OPEN. Corrected-core-value-continuation §V4 is an informative research draft, not semantic authority.
- Exact Lean definitions read: OperationDeclarationResolved, OperationDeclaration.instantiate, PaperComputationTyped.perform/request and PaperContinuationTyped.continuation; R28 TermSubstitutionTyped/termSubstituteComputation/PaperComputationTyped.termSubstitute; R36 State/StackTyped/StateTyped/plug/erase; R45 bounded control/erasure/finite-prefix interfaces.

## Frozen artifacts and proof-only boundary

- Module: `notes/theory/lean/YulangClosure/PaperPerformLetExecution.lean`, SHA `fba6990df8444daa163bdc6ec88892bde669072552ac15fef0b26eec81c8e2b7`.
- Audit: `notes/theory/lean/.lake/R47Audit.lean`, SHA `8e82040c4345c8c80d73ff1006e9329ad7e6cb8963df5114b2873eb36890f5a1`; byte-identical frozen R46 audit source.
- Worker receipt: `tasks/agent-loop/inbox/paper-perform-let-r47-worker.log`, SHA `5cca4a0830d8777bedc447b581a706569552655e0993d69bc23bf4424f9d5b52`.
- All 37 public and 3 private theorem headers are byte-identical through `:=` to the R46 seed. Every definition/inductive and all non-proof structure are unchanged. Only proof terms changed. No root import, Rust, dependency, manifest, toolchain, question, test or shared status edits.
- Startup script verified 9 source/environment entries plus the 3 frozen R46 artifacts; the primary supplied complete pre-lease source verification. The worker's final explicit complete 12-source/environment pin check matches every expected hash. The startup script omitted manuscript/R45/root from its own initial source list; no claim of an initial worker-complete 12-source check is made. Full actual initial/final lists are in the worker log.

## Actual process receipt

All cwd: `/tmp/yulang-r47-perform-let-repair/notes/theory/lean`. Native resolved Lake: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`. Read-only `elan which lake` lookup exited 0. Lake version `5.0.0-src+eb6cafb (Lean version 4.35.0)`; Lean `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release. Every process launch records exact argv, cwd, UTC, timeout, thread environment and candidate hash; completion records monotonic duration, exit, timeout status and complete raw stream paths/hashes. Full stdout/stderr bytes reside in the enumerated files below. LEAN_NUM_THREADS=1, project/explicit `-j1 -M1024`.

| Call | Native Lake arguments | Exit | Monotonic seconds |
| --- | --- | --- | --- |
| 1 | `--version` | 0 | 0.414746044997 |
| 2 | `env lean --version` | 0 | 0.114232341999 |
| 3 | `build +YulangClosure.PaperPerformLetExecution` | 1 | 31.179652703002 |
| 4 | `build +YulangClosure.PaperPerformLetExecution` | 0 | 1.066220925997 |
| 5 | `env lean -j1 -M1024 .lake/R47Audit.lean` | 1 | 3.019992836002 |

Raw process logs (all under tasks/agent-loop/inbox):

- `paper-perform-let-r47-call-01.stdout`: `165f92ed239a8c7db772bf5ee9d58c59357b489951582a12c86dc9d8e06b23a2`.
- `paper-perform-let-r47-call-01.stderr`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `paper-perform-let-r47-call-02.stdout`: `eb22144228dd41cd51a0c84af4f976cd0cef473102dcf99b60be756b11f2b95a`.
- `paper-perform-let-r47-call-02.stderr`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `paper-perform-let-r47-call-03.stdout`: `ed9368be6fe7b1306c81b842811ffb7dae660c54c8148b531b9e4d672275791f`.
- `paper-perform-let-r47-call-03.stderr`: `c4a27db198c4d8632369ee6102944ef46e83c20d685f7c17a6aaff9cfcfc710f`.
- `paper-perform-let-r47-call-04.stdout`: `27f1319be62f05f92a18c7ec4e8e20bcc181a48795e5ef0d5ca1d8dd37ee993b`.
- `paper-perform-let-r47-call-04.stderr`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `paper-perform-let-r47-call-05.stdout`: `29e0019f281362e73a2e771d42d699b7107a8507163678b99e2616492fdcafe9`.
- `paper-perform-let-r47-call-05.stderr`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

Total literal Lean/Lake calls: 5/10. Total checker seconds: 35.794844851996/120. No timeout. One failed construction build of the allowed two, followed by successful final candidate build, followed by the single strict audit. Active runtime stayed below the 1200-second grant; version launch to final write-cessation confirmation was below 400 wall seconds. Main-worktree Lean and tests: NOT_RUN. The bundled helper was not invoked because it would repeat calls and does not implement this stricter exact two-axiom whitelist; the supplied strict audit uses theorem-kind checks, full explicit types, complete #print axioms and Lean.collectAxioms.

## Preserved failures and exact remaining obligation

Construction call 3 failed only at constructor-case binder naming (unknown declaration/resolved/arity) and a do-bind unreduced by restricted simp. Complete diagnostics remain in call-03.stdout. Proof-only repairs named the actual declaration with `rename_i`, passed the request arguments explicitly and reduced do notation with a definitional `change`; call 4 built all 13 target jobs successfully. Resolver Boolean-case proof, explicit continuation witnesses, simultaneous response insertion and nullary induction branches compiled.

Strict audit call 5 failed. It printed all 37 theorem types and all 37 complete axiom lists, but only 26 END markers. There are 12 actual error diagnostics:

1. `.lake/R47Audit.lean:7:0`: `Unknown option pp.width` in the inherited frozen audit source.
2. Eleven public theorem transitive axiom sets contain `Classical.choice`, outside the contract's exact whitelist `{propext, Quot.sound}`. The first is resolveOperation_iff; dependent perform/preservation/result discriminators also carry it. A successful build alone does not satisfy the contract. No exact axiom-origin audit of private/library dependencies was run after mandatory stop; do not infer a cause solely from source spelling.

The first remaining bounded obligations are a valid pinned audit printer option and proof-term elimination/localization of Classical.choice while preserving every definition and theorem statement. Owner: primary dispatch of a new bounded packet. No permission request is needed within the user's continuing authority, but this worker's fixed packet stopped. Do not widen the whitelist or promote this module on this receipt.

## Scope and parent application

Namespace: YulangClosure.PaperTypes.PaperPerformLetExecution. The unchanged perform_through_stack quantifies shared d/g/e, declaration, operation/type arguments/payload, response binder, arbitrary finite StackTyped stack and outer final type; one declaration instance supplies operation identity, payload and response, and the exact emitted identity continuation is propagated to a final typed request. Request response, continuation normal-result and final stack result remain distinct indices. The checked module constructs the bounded derivation, but failed strict acceptance prevents a proof-closure claim.

Represented cases: existing R36/R45 successful steps; perform; empty-owner request continuation through arbitrary finite ordinary let stacks; simultaneous R28 insertion fixing 0 and shifting n+1 to n+2; innermost-first stored frame order; preservation at finite prefixes; erasure; duplicate-identical declaration acceptance/conflicting same-identity rejection; arity rejection; shared instance fields; distinct result types; two-frame order; insertion capture discriminator; nonempty-owner rejection; unsupported raw bodies rejected by the existing partial operation.

Omitted/open: general owner/handler alpha-renaming, nonempty-owner propagation, remaining full-paper constructors and frames, full-state/current-port/residual-graph simulation, source-owner closure, source/native and Rust correspondence, inference A/B, whole executor, production. The original manuscript :1860–1877 parent still needs corrected full-paper state-to-finite-let simulation and current-port/residual-graph evidence from their actual owners. No LocalLaws instance or whole-language claim was established.

## Complete public axiom results

All fully qualified names have prefix `YulangClosure.PaperTypes.PaperPerformLetExecution.`. Complete full explicit theorem types, including hypotheses/quantifiers, are preserved verbatim in call-05.stdout. This table records every printed axiom result, including rejected ones.

| Theorem | Actual complete axioms |
| --- | --- |
| `resolveOperation_iff` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `performStep_eq` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `performStep_arity_mismatch` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `perform_applicable` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `perform_preservation` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `insertResponse_zero` | `[]` |
| `insertResponse_outer` | `[]` |
| `insertResponse_typed` | `[propext, Quot.sound.{u}]` |
| `requestBind_applicable` | `[propext, Quot.sound.{u}]` |
| `requestBind_preservation` | `[propext, Quot.sound.{u}]` |
| `controlStep_extends` | `[propext, Quot.sound.{u}]` |
| `controlStep_evidence` | `[propext, Quot.sound.{u}]` |
| `evidence_preservation` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `preservation` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `plug_step` | `[propext, Quot.sound.{u}]` |
| `evidence_erasure` | `[propext, Quot.sound.{u}]` |
| `erasure` | `[propext, Quot.sound.{u}]` |
| `trace_preservation` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `perform_empty_owner` | `[propext, Quot.sound.{u}]` |
| `requestBind_shape` | `[propext, Quot.sound.{u}]` |
| `controlStep_request_nil` | `[propext, Quot.sound.{u}]` |
| `controlStep_request_cons` | `[propext, Quot.sound.{u}]` |
| `requestTrace_empty_owner` | `[propext, Quot.sound.{u}]` |
| `perform_requestTrace_empty_owner` | `[propext, Quot.sound.{u}]` |
| `requestTrace_trans` | `[propext, Quot.sound.{u}]` |
| `propagate_stack` | `[propext, Quot.sound.{u}]` |
| `perform_through_stack` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `perform_controlTrace_empty_owner` | `[propext, Quot.sound.{u}]` |
| `nonempty_owner_rejected` | `[propext, Quot.sound.{u}]` |
| `external_request` | `[]` |
| `two_frames_order` | `[propext, Quot.sound.{u}]` |
| `repeated_declarations_resolve` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `conflicting_declarations_rejected` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `one_instance_fields` | `[]` |
| `distinct_result_types` | `[]` |
| `insertion_discriminator` | `[propext, Quot.sound.{u}]` |
| `unsupported_body_rejected` | `[propext, Quot.sound.{u}]` |

## Writes and handoff

Exact authored paths: module, `.lake/R47Audit.lean`, this handoff, worker log, `paper-perform-let-r47-call-01.stdout/.stderr` through `paper-perform-let-r47-call-05.stdout/.stderr`, and dedicated `.lake/build` generated outputs. No other writes. No descendants or pending worker-owned runtime processes. Module/audit/checker writes stopped after audit failure; explicit cessation confirmed at 2026-10-25T21:02:15.847854+00:00. Worker state STOPPED after this frozen handoff. Remaining resources are not permission to repair after audit failure. Preserve candidate, successful build, failed audit, and all material raw failures as research evidence; primary review/integration remains NOT_RUN.
