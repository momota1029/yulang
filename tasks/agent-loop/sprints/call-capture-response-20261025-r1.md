# LEAN-CALL-CAPTURE-RESPONSE-20261025/r1 — response cancellation and typing

Status: **FROZEN by Luna; author activation follows exact lease acknowledgment.**
Branch/baseline: `research/simple-sub-intrusion` / `79e71c17d`.
Authority: unchanged Yulang source semantics; existing Call syntax and typing definitions below. This packet does not add or change a semantic rule.

## Original goal and the next parent-facing result

The unchanged user goal is complete Lean proofs of Yulang semantics and type inference over the accepted source domain. The current Call formalization has an actual `CallState.captureFrames` operation for an externally requested continuation. A requested state carries the continuation under a response binder; the operation captures the actual Call frames, inserting that binder around bind/adapter bodies. This sprint proves that supplying a response cancels the inserted binder and that the captured continuation remains well typed.

The direct parent-facing gap is response substitution through the existing captured Call continuation. The sprint establishes syntax-level cancellation and typing for arbitrary existing frame lists. It does **not** establish that an external source/native resumption supplies a correctly typed response or lawful metadata, and it does not close Call A/B or source/native correspondence.

## Frozen source owners and dependencies

All pins were revalidated against the baseline before issuing author leases:

| Input | SHA-256 |
|---|---|
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

The two proposed statements were separately audited against these source owners by read-only Sol explorers. Those audits are proposal evidence only, not proof certification. Existing `CallStepTypingRepair.captureBind_typed` is private and cannot be imported as an API; its response-binder construction is a source-level precedent. Existing `TypedCall.contextTyping_plugFrames` is accepted but cannot directly type the captured syntax without accounting for the response binder and `captureBind` renaming. Q therefore proves the capture judgment directly by induction.

Relevant definitions: `TypedCall.upCall`, `renameCallComp`, `liftCallSubstitution`, and `substituteCallComp` are in `CoreSubstitution.lean:522–603`; `CallState.captureBind` is in `ControlSyntax.lean:144`; `CallState.captureFrames` is in `CallRequestUnwind.lean:7–18`; `ContextTyping` is in `CoreSyntax.lean:297–310`.

## Exact propositions

Use this abbreviation in the P and Luna modules:

```lean
abbrev responseSubstitution (v : TypedCall.Value) : Nat → TypedCall.Value :=
  fun i => if i = 0 then v else .var (i - 1)

abbrev plugResponse (k : TypedCall.Comp) (v : TypedCall.Value) :
    TypedCall.Comp := TypedCall.substituteCallComp (responseSubstitution v) k
```

### P — capture/bind cancellation

Author `/root/call_response_cancellation_prover`, Sol/high. Preserve the unrestricted proposition:

```lean
theorem captureBind_response_cancellation
    (k body : TypedCall.Comp) (v : TypedCall.Value) :
    plugResponse (CallState.captureBind k body) v =
      .bind (plugResponse k v) body
```

No typing, closedness, value-shape, or metadata premise may be added. In particular this must hold for open `k`, `body`, and `v`. The proof is Call-specific mutual syntax induction: cancellation of `substituteCallComp s` against `renameCallComp r` under the pointwise inverse law `s (r i) = .var i`, with its lifted version under bind/request binders. Specialize to `s := liftCallSubstitution (responseSubstitution v)` and `r := upCall Nat.succ`. Do not claim an Original/raw syntax bridge.

Lease exactly:

- `notes/theory/lean/YulangClosure/CallResponseCancellation.lean` (import `YulangClosure.ControlSyntax`)
- `tasks/agent-loop/inbox/20261025-call-response-cancellation.md`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallResponseCancellation.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallResponseCancellation.ilean`

Falsifiers to cover in review: changing the response index from zero; replacing `upCall Nat.succ` by `Nat.succ`; changing the order of two captured bind bodies. The proposition must fail under these mutations on explicit open syntax witnesses.

### Q — captured-frame typing

Author `/root/call_capture_typing_prover`, Sol/high, independent of P's source file. Preserve the public specialization:

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

A private helper may generalize `Original.emptyContext` to any `env`. Prove by induction on `hframes`, generalizing `k`, covering exactly `nil`, `bind`, `adapter`, `scope`, and `expose`. For bind/adapter, type the actual `captureBind` using `renameCallComp_typed` with `upCall Nat.succ`; do not shift the body with `Nat.succ`. Scope/expose preserve the actual frame constructors and both expose views. No added source authenticity, effect-row, runtime-resumption, or response-law premise.

Lease exactly:

- `notes/theory/lean/YulangClosure/CallCaptureTyping.lean` (import `YulangClosure.CallRequestUnwind`)
- `tasks/agent-loop/inbox/20261025-call-capture-typing.md`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallCaptureTyping.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallCaptureTyping.ilean`

Falsifiers to cover in review: wrong response-binder lifting and reversed frame order (including a bind/adapter mismatch).

### Luna composition

After P and Q authors STOP, Luna owns only:

- `notes/theory/lean/YulangClosure/CallCaptureResponse.lean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallCaptureResponse.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallCaptureResponse.ilean`
- `notes/theory/lean/.lake/call-capture-response-r1-check.lean`
- `tasks/agent-loop/inbox/20261025-call-capture-response-r1-verification.jsonl`
- `tasks/agent-loop/inbox/20261025-call-capture-response-r1-review.md`
- `tasks/agent-loop/sprints/call-capture-response-20261025-r1-outcome.md`

Prove the all-frame equation:

```lean
plugResponse (CallState.captureFrames frames k) v =
  TypedCall.plugFrames frames (plugResponse k v)
```

for arbitrary frame lists, computations, and values. Use P for `.bind` and `.adapter`; preserve `.scope` and both `.expose` views in their actual order.

Then prove the typed consequence using Q, actual response typing, and `substituteCallComp_typed`:

```lean
(hframes : TypedCall.ContextTyping Original.emptyContext frames a b)
(hk : TypedCall.CompTyped
  (Original.extend Original.emptyContext response) k a)
(hv : TypedCall.ValueTyped Original.emptyContext v response) :
TypedCall.CompTyped Original.emptyContext
  (TypedCall.plugFrames frames (plugResponse k v)) b
```

This is a reusable syntactic response-plugging result. It does not assert that a runtime/source response exists.

## Verification and review

Fresh sprint ceiling: **3,000 seconds**, partitioned as P 900 + Q 600 + Luna composition 240 + serialized Lean verification 480 + independent review 600 + integration 180. No prior budget carries forward. Astra: 0. Maximum two authors simultaneously; three UNKNOWN quarantines remain unchanged. Activate the fresh reviewer only after both authors STOP and candidate hashes freeze.

At most four serialized Lean invocations in this order: P, Q, composition, exact signature/axiom query. Each is one process/CPU, 1 GiB, timeout 120 seconds. Use `lake env lean` directly, pass exact leased `.olean`/`.ilean` output paths, capture full streams/exit/timeout/timestamps/source/input/output hashes, append and fsync each receipt row before continuing. Stop at the first failure, pin mismatch, signature drift, missing output, timeout, or unapproved axiom. Allowed axioms: `[propext, Quot.sound]` or a subset. No tests or production build are authorized.

Fresh nonauthor `compiler_referee` reviews the frozen P/Q/composition sources, exact query and complete receipt. Acceptance requires all four checks exit 0, exact propositions and quantifiers, no holes/custom axioms, hash/receipt consistency, all frame cases and binder indices correct, and CLEAN review. The row-2 clock anomaly from the prior sprint is historical only; all r1 timestamps must be internally monotone with monotonic duration.

## Scope, implementation lane, and stop conditions

No compiler/runtime change is authorized. The proposed law is in existing syntax and typing only. Adding or changing a Force/View/Call transition would alter semantics and is outside this contract. The operational Force/View source clause and current `ControlSyntax` transition relation remain separate authorities; this sprint does not reconcile them.

The only productive in-sprint lane is constructive proof plus independent falsification/review. There is no safe production-code slice: the proposed equalities/typing judgment do not establish source/native response behavior, and new runtime behavior would need separate source correspondence and semantic approval. No Rust edit, source-domain restriction, Call A/B promotion, inference A/B promotion, or production authorization follows.

Stop authors after their frozen source/handoff and report resource usage, then freeze the review snapshot. Stop the sprint at a genuine counterexample, source mismatch, first failed Lean command, unexpected axiom, exhausted budget, or CLEAN adjudication. Consult the dispatcher at the next material obstruction, authority/dependency/lease change, integration seam, or sprint boundary.
