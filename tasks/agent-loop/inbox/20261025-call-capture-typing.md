# CALL-CAPTURE-TYPING-20261025-Q — frozen handoff r1

- Sprint: `LEAN-CALL-CAPTURE-RESPONSE-20261025/r1`.
- Contract: `tasks/agent-loop/sprints/call-capture-response-20261025-r1.md`, SHA-256 `af006b81aa906e5017f23c3b15e754ac603355745372b283e220f93a5fcb5c49`.
- Assignment/handoff ID: `CALL-CAPTURE-TYPING-20261025-Q`, revision `1`.
- Contract baseline: `79e71c17d`; parent-issued current checkpoint: `ccd5a9891`, branch `research/simple-sub-intrusion`. No Git command was used; the exact dependency bytes below matched the frozen contract.
- Author/actual worker identity: `/root/call_capture_typing_prover`, role `prover`; no contributing descendants or coauthors. Current session locator: `LEAN-CALL-CAPTURE-RESPONSE-20261025/root-turn-14`, read from current state; activation was the parent assignment and this worker's lease acknowledgment.
- Requested model/effort: Sol/high. Observed effective model/effort: `UNKNOWN`/`UNKNOWN`; no model metadata was returned to this worker.
- Outcome class: **candidate** Lean proof source. It has not been elaborated or independently reviewed; it is not a reviewed theorem or production authority.

## Parent claim and immediate application

The unchanged parent-facing claim is that response substitution through an arbitrary existing captured Call continuation cancels the inserted response binder and preserves typing. The unchanged broader goal is complete Lean proofs of Yulang semantics and inference over the accepted source domain. This packet supplies exactly Q, continuation typing under the response binder, for Luna's composition with P and `TypedCall.substituteCallComp_typed`.

The public declaration, in namespace `YulangClosure.Control`, is exactly:

```lean
theorem captureFrames_typed
    {frames : List TypedCall.ContextFrame}
    {response a b : Original.Ty}
    {k : TypedCall.Comp}
    (hframes :
      TypedCall.ContextTyping Original.emptyContext frames a b)
    (hk : TypedCall.CompTyped
      (Original.extend Original.emptyContext response) k a) :
    TypedCall.CompTyped
      (Original.extend Original.emptyContext response)
      (CallState.captureFrames frames k) b
```

No hypothesis was added. The private `captureFrames_typed_env` generalizes only the ambient environment. Its private `captureBind_response_typed` helper uses the actual `CallState.captureBind`, hence `renameCallComp (upCall Nat.succ)`, and `renameCallComp_typed`. The environment equality is proved at index zero and at successors by definitional equality: the local body binder remains zero, and every ambient index moves past the inserted response binder.

All five `ContextTyping` cases occur explicitly:

| Case | Actual construction and application |
| --- | --- |
| `nil` | `captureFrames [] k` is definitionally `k`; retain `hk`. |
| `bind` | Type `captureBind k body` with the private helper, then apply the tail induction hypothesis. |
| `adapter` | The same actual `captureBind` construction, retaining the frame derivation's input/output types, then apply the tail hypothesis. |
| `scope` | Type `.scope owner k` using `CompTyped.scope`, then apply the tail hypothesis. |
| `expose` | Type `.expose effectView resultView k` using `CompTyped.expose`, preserving both actual views and their order, then apply the tail hypothesis. |

The induction generalizes `k` and follows the actual head-frame-then-tail order. There are no missing mathematical frame cases in this candidate. Remaining Q premise: successful Lean elaboration and exact signature/axiom checking, then fresh independent review, owned by Luna under the contract. P, the all-frame cancellation equation, and the typed response-plugging consequence remain separate pending composition work.

## Exact source evidence and boundaries

Read owners: `CoreSyntax.lean` (`Original.extend`, `TypedCall.CompTyped`, `TypedCall.ContextTyping`), `CoreSubstitution.lean` (`upCall`, `renameCallComp`, `renameCallComp_typed`, response-substitution typing API), `ControlSyntax.lean` (`CallState.captureBind`), and `CallRequestUnwind.lean` (`CallState.captureFrames`). The formal capture operation is already used by `call_request_unwind_exists`; the Q proof reasons about this actual syntax constructor, not an assumed replacement transition.

The constructor/transport/consumer path for Q is `ContextTyping.bind/adapter/scope/expose` → actual `captureBind`/`captureFrames` → existing Call renaming and computation typing → Luna's forthcoming typed response-plugging consequence. No constraint-generation, inference propagation, source authenticity, metadata, native execution, or external response-supply law is asserted by Q. No source/native correspondence or runtime response evidence was obtained. Call A/B, inference A/B and production gates stay OPEN. The source/native response supplier and metadata law are outside this packet; Luna owns assigning their actual source/consumer symbols in a separate authority envelope.

Prior work reused within its premises: the binder construction in private `CallStepTypingRepair.captureBind_typed` was a source-level proof precedent, generalized here to arbitrary `env`; it was not imported as a public API. The induction shape of accepted `TypedCall.contextTyping_plugFrames` was reused. Its theorem was not applied directly because ordinary plugging lacks the inserted response binder. No historical failure or assumed operational transition was used as evidence of actual source behavior. P's source file was neither read nor imported.

## Dependency pins and frozen artifact

All paths in this pin table are relative to `notes/theory/lean/`:

| Input | SHA-256 |
| --- | --- |
| `YulangClosure/CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `YulangClosure/CoreSubstitution.lean` | `c4bca75be173f20d7a48751205f488ac5f0057b476e6f52d1ef7abcf046a001a` |
| `YulangClosure/CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `YulangClosure/ControlSyntax.lean` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| `YulangClosure/CallRequestUnwind.lean` | `e4835bd2c2487b14d658b02373e0507ea6c201b81a1fb81d396b0f05a1850fc9` |
| `YulangClosure/CallContextTyping.lean` | `09bc05fc8561ee81186dd6eae3667a77b0360a8dd27a6236548dfb01d33a5125` |
| `YulangClosure/CallStepTypingRepair.lean` | `2ef522c022a0708be670f1ab44b57c8f558d4736f123e14ceb5f6ff259a3c586` |
| `lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| `lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |

Frozen candidate source: `notes/theory/lean/YulangClosure/CallCaptureTyping.lean`, SHA-256 `906e8204aa155efd3f4e45d9c2a2a9fbe010858206ef3dd0acfd3d0d607a0de9`. Author: `/root/call_capture_typing_prover`. Direct import: only `YulangClosure.CallRequestUnwind`. This source is immutable after submission unless Luna issues a new revision.

## Checks, falsifiers and resources

Performed: narrow source inspection, exact SHA-256 pin comparison for all ten inputs and contract, source readback, and observation that both Q generated outputs are absent. Lean/compiler invocations: **0**. Tests: **0**. Production builds: **0**. Probe processes: **0**. Git commands: **0**. Descendants: **0**. No `sorry`, `admit`, custom axiom, semantics change or extra theorem hypothesis was inserted. These are author checks, not independent proof certification.

Review falsifiers supplied as unexecuted syntax witnesses:

1. Wrong response-binder lifting: let `U := .base .unit`, `response := .thunk U`, `k := .ret (.original .unit)`, and `body := .ret (.var 0)`, with one bind frame from `U` to `U`. Correct `upCall Nat.succ` retains the body's index zero. A mutation using `Nat.succ` yields `.ret (.var 1)` under the target body's context `[U, thunk U]`, which has type `thunk U` rather than the required `U`.
2. Reversed order, including bind/adapter mismatch: let `U := .base .unit`, `liftBody := .ret (.delay (.ret (.var 0)))`, `forceBody := .force (.var 0)`, and `frames := [.bind liftBody, .adapter (.thunk U) U forceBody]`. This list is typed from `U` to `U`; use the same unit-returning `k`. Correct capture first creates a thunk and then forces it. Reversed capture forces the initial `U` value before the thunk-producing bind, so the inner force cannot satisfy its required thunk typing. These witnesses are for the frozen review; they were not run as tests or added as files.

Q's grant is 600 seconds, with no renewal and no Astra allocation. The first locally instrumented timestamp was monotonic `15084.353133106`; a later source-freeze readback was `15154.250710358` (69.898 seconds of observed interval). Startup reading before that anchor was not timed, so total actual active duration is **UNKNOWN**. Conservatively retain/charge the entire 600-second grant and reclaim zero seconds; this handoff does not request more time. Generated outputs remain for Luna's serialized verification after the writer stops.

## Mutual TODOs, next step and STOP receipt

- `Q-VERIFY-1`: Luna checks the exact Q theorem using the contract's second serialized Lean invocation and exact leased outputs; falsifier is any elaboration failure, signature drift, unexpected axiom, pin mismatch, missing output or timeout. Inputs are the frozen source and pins above. No worker-run check is authorized.
- `Q-COMPOSE-1`: Luna applies Q, P's independently frozen cancellation result, actual response typing, and `substituteCallComp_typed` to the original typed response-plugging obligation. Its output is the already leased `CallCaptureResponse.lean`; failure to preserve arbitrary existing frame lists or the response binder is the falsifier.
- `Q-REVIEW-1`: Luna assigns a fresh nonauthor review of frozen P/Q/composition and verification receipts, covering all five frame cases and the two mutation witnesses above. This author is ineligible to certify the combined result.

All new/written paths are exactly:

- `notes/theory/lean/YulangClosure/CallCaptureTyping.lean`
- `tasks/agent-loop/inbox/20261025-call-capture-typing.md`

Other exact leased paths, deliberately not generated:

- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallCaptureTyping.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallCaptureTyping.ilean`

Scratch paths: none. No other path was written. No child writer or descendant lease exists. **STOP / WRITE CESSATION:** source and handoff are frozen at this submission; no further writes or checks will be performed by this assignment. The next stage belongs to Luna; the author is not running while waiting. Candidate is preservation-ready as unverified research, with elaboration, independent review and integration pending. No parent gate is declared closed.
