# R49 perform/let proof finalization

Handoff revision 1. Outcome: CHECKER_ACCEPTED / STOPPED; primary verification and independent review NOT_RUN. This worker does not certify integration or close the whole-language parent.

## Fixed authority and mapping

Worker `/root/r49_perform_let_finalize`, registered lean_prover leaf, no descendants; requested/observed model and effort UNKNOWN from runtime metadata. Exact baseline `a955e74ffee83560204b74b91e2154e8076f5fa1`; isolated checkout `/tmp/yulang-r49-perform-let-finalize`. Contract `tasks/agent-loop/sprints/paper-perform-let-finalize-r49.md` SHA `25712855fab407813a89d0970b2bde50e07625fbf6ac1bba8ca236596a565dc4`. Root/base instructions, sprint rules, design authority, Lean proof skill/source/execution references, manuscript corrections, actual Lean interfaces, previous failure and pinned library source were read. No root import, compiler, dependency, test, Git, question or shared-state writes.

Original manuscript `docs/yulang-operational-type-safety-ja.tex` SHA `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`: source-owner correction :54–63, perform :318–319, request bind :340–359, frame plugging :1012–1026, request extraction :1047–1066; full-state/current-port/residual-graph parent :1860–1877 remains OPEN. Corrected continuation note V4/V5 distinguishes retained evidence and execution owner, and retains response/normal-result types; these research drafts add no semantic authority.

Lean namespace `YulangClosure.PaperTypes.PaperPerformLetExecution`. Relevant interfaces are `OperationDeclarationResolved`, `OperationDeclaration.instantiate`, `PaperComputationTyped.perform/request`, `PaperContinuationTyped.continuation`, R28 `TermSubstitutionTyped`, R36 `StateTyped/StackTyped/plug`, and R45 `PaperTupleSplitExecution`. Declaration resolution accepts repeated identical entries and rejects conflicting same-id entries. Every payload/response/identity field uses one declaration instance.

## Exact repair and acceptance

Only two proof witness constructions changed from the R48 seed. In private `find_resolved` and public `resolveOperation_iff`, `List.find?_some` now receives `(p := fun entry : OperationDeclaration => entry.identity == operation) (a := candidate) (l := operations)`, yielding explicitly typed Boolean equality; `Nat.eq_of_beq_eq_true` supplies Nat equality. Pinned source consulted: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean/Init/Data/List/Find.lean:297` and `Init/Data/Nat/Basic.lean`. The first proof build passed; no repair retry or dependency-diagnostic call was needed.

All 40 theorem headers (37 public, 3 private) match the R48 seed byte-for-byte through `:=`. The exact diff consists solely of the two proof fragments; all definitions, inductives, assumptions, quantifiers, declaration semantics, frame order, response insertion and owner scope remain unchanged. The audit source is byte-identical to R48's corrected source. Before/after verification matched all 12 source/environment pins plus audit; the candidate seed and R48 handoff pins also matched.

Final strict audit call 4 exited 0: all 37 public declaration-kind checks, complete printed types, complete `#print axioms` results, whitelist checks and 37 BEGIN/END pairs passed. Exact whitelist remains `{propext, Quot.sound}`; no Classical.choice, sorryAx or project axiom dependency. Complete types and axiom lists are retained in call-4 raw stdout. The manual strict audit was used because the bundled helper permits a broader axiom set and repeats checks.

Axiom-free public targets (5): `insertResponse_zero`, `insertResponse_outer`, `external_request`, `one_instance_fields`, `distinct_result_types`.

Exact `[propext, Quot.sound]` targets (32): `resolveOperation_iff`, `performStep_eq`, `performStep_arity_mismatch`, `perform_applicable`, `perform_preservation`, `insertResponse_typed`, `requestBind_applicable`, `requestBind_preservation`, `controlStep_extends`, `controlStep_evidence`, `evidence_preservation`, `preservation`, `plug_step`, `evidence_erasure`, `erasure`, `trace_preservation`, `perform_empty_owner`, `requestBind_shape`, `controlStep_request_nil`, `controlStep_request_cons`, `requestTrace_empty_owner`, `perform_requestTrace_empty_owner`, `requestTrace_trans`, `propagate_stack`, `perform_through_stack`, `perform_controlTrace_empty_owner`, `nonempty_owner_rejected`, `two_frames_order`, `repeated_declarations_resolve`, `conflicting_declarations_rejected`, `insertion_discriminator`, `unsupported_body_rejected`.

## Parent application

The checked bounded parent retains this exact type:

```lean
theorem perform_through_stack {d g e declaration operation arguments payload binder stack final}
    (resolved : OperationDeclarationResolved d.operations operation declaration)
    (arity : arguments.length = declaration.typeArity)
    (hp : PaperValueTyped d g e payload (declaration.instantiate arguments).payloadType)
    (hf : StackTyped d g e stack (declaration.instantiate arguments).responseType final) :
    ∃ saved,
      performStep d binder (.perform operation arguments payload) =
        some (.request (declaration.instantiate arguments) payload
          (.continuation [] binder (.ret (.variable 0)))) ∧
      RequestTrace
        ⟨.request (declaration.instantiate arguments) payload
          (.continuation [] binder (.ret (.variable 0))), stack⟩
        ⟨.request (declaration.instantiate arguments) payload (.continuation [] binder saved), []⟩ ∧
      PaperComputationTyped d g e
        (.request (declaration.instantiate arguments) payload (.continuation [] binder saved)) final
```

It constructs a perform identity continuation and absorbs every finite typed ordinary let stack, preserving the shared declaration instance, d/g/e and final result type. Supporting theorems establish executable one-step/finite-prefix preservation, source-shaped erasure, empty-owner propagation and external typed requests. Discriminators cover repeated/conflicting declarations, arity mismatch, distinct response/continuation/final types, two lets in innermost-first order, binder 0 preservation and n+1→n+2 capture avoidance, nonempty-owner rejection and unsupported-body rejection.

The first remaining acceptance premise is the primary's isolated 4-call verification followed by fresh independent review; owner Luna. Nonempty owner alpha-renaming, handlers and omitted constructors/frames, full-state/current-port/residual graph, source-owner/source-native correspondence, inference A/B, Rust and production remain OPEN. No native constructor or production consumer was inspected; no implementation bridge is claimed. R46/R47/R48 remain FAILED; R45 remains unchanged.

## Process and resources

All call cwd `/tmp/yulang-r49-perform-let-finalize/notes/theory/lean`. Read-only `elan which lake` resolved the installed native executable `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`. Lake `5.0.0-src+eb6cafb (Lean version 4.35.0)`; Lean `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release. Each call logs exact argv, cwd, monotonic launch/completion duration, exit, raw-stream hashes and 60-second maximum; proof/audit launches additionally record artifact hashes. All use LEAN_NUM_THREADS=1; build/direct checks use project/direct `-j1 -M1024`. No timeout or failed checker call occurred.

| Call | Native Lake arguments | Exit | Monotonic seconds |
| --- | --- | --- | --- |
| 1 | `--version` | 0 | 0.415085161003 |
| 2 | `env lean --version` | 0 | 0.114044043003 |
| 3 | `build +YulangClosure.PaperPerformLetExecution` | 0 | 30.480696858998 |
| 4 | `env lean -j1 -M1024 .lake/R49Audit.lean` | 0 | 2.968452859001 |

Literal calls 4/6; checker seconds 33.978278922004/90. One repair build; optional dependency call unused. Logged pin-verification-to-stop elapsed 120.561s; preceding instruction/source reads additional, total below 600 active seconds. No further checker calls are authorized or needed inside this completed packet.

## Frozen files

- Candidate `notes/theory/lean/YulangClosure/PaperPerformLetExecution.lean`: `2f0026049554cb870158115b4bab8d42f7cbee8b030ee3f84a904763c328cac0`.
- Audit `.lake/R49Audit.lean`: `be0a8400df0f3696791f4ae4c176738fb9d38a2ee7e7a307b7a50f8df5b09c2e`.
- Worker log `tasks/agent-loop/inbox/paper-perform-let-r49-worker.log`: `cc9fc2cd7e7f8951f34dd58c3b7d5d423080b8a792074557300107900e708e5a`.
- Call 1 stdout `paper-perform-let-r49-call-1.stdout`: `165f92ed239a8c7db772bf5ee9d58c59357b489951582a12c86dc9d8e06b23a2`; stderr `paper-perform-let-r49-call-1.stderr`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- Call 2 stdout `paper-perform-let-r49-call-2.stdout`: `eb22144228dd41cd51a0c84af4f976cd0cef473102dcf99b60be756b11f2b95a`; stderr `paper-perform-let-r49-call-2.stderr`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- Call 3 stdout `paper-perform-let-r49-call-3.stdout`: `87a10a23dcf5fc0ae47cdd1638263724864ca30ee793a8cf776580ae14f4859a`; stderr `paper-perform-let-r49-call-3.stderr`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- Call 4 stdout `paper-perform-let-r49-call-4.stdout`: `cb61cc9f38bff07dc0aed764a5ce005b3b8057eaf92efa18da39bc5d73e5531a`; stderr `paper-perform-let-r49-call-4.stderr`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

Generated outputs are confined to the leased `.lake/build` cache. No `R49DependencyCheck.lean` was created. Source search found no sorry/admit/project axiom/unsafe/native bypass in the candidate; audit “axiom” occurrences are rejection strings and intentional #print commands. No tests ran.

Worker STOPPED at 2026-10-25T21:13:36.269508+00:00. All writes cease with this handoff; no descendants or unresolved worker leases. Primary can copy the byte-identical candidate and audit into its fixed isolated checkout for the prescribed verification/review. No worker-side Git action occurred.
