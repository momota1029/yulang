# Independent review: LEAN-CALL-REQUEST-BOUNDARY-20261025/r2

Verdict: **CLEAN**. No blocking, major or minor finding in the frozen proof component. This is a source-first independent proof/conformance review, followed by read-only hash and receipt inspection; no Lean invocation, test or build was rerun.

Assignment: `/root/call_request_boundary_review_astra_r2`, handoff revision 1.
Contract SHA-256: `b92747b9e519be2f9f3c14c01db0f1353a0a3ea461fb8633b0d25eb2ff27896f`.
Inherited r1 contract SHA-256: `b3113904ec188ab90455f2af0d702541ee6c50ce2c6a49e3919fcbff4bd90775`.
Observed HEAD: `4d15e26ff207993a8e9049fb21f754f219c0a273`; branch: `research/simple-sub-intrusion`.
Requested reviewer model/effort: `gpt-6-astra` / `medium`. Effective observed model/effort: **UNKNOWN / UNKNOWN**; no runtime model metadata was supplied to this reviewer. Labels do not authenticate models or historical authorship. The reviewer made no contribution to the frozen proof/query/checker artifacts.

## Source argument and original scope

I inspected `ControlSyntax.lean`'s actual `CallControlStep` constructors, `CallState.initial`, `captureBind`, and state fields; the snoc-oriented length-indexed `Prefix` in `Contracts.lean`; and `captureFrames` in `CallRequestUnwind.lean` before assessing the new results.

`requestNext` matches all four frame transitions and `finishRequest` exactly. Bind and adapter capture retain `upCall Nat.succ`; scope suspension prepends its owner; expose suspension uses the effect occurrence identity, retains both occurrences in captured syntax and does not change observations. Suspension actions and continuation capture consume the innermost frame first. `finishRequest` alone replaces `viewContext` with the original observed list. The partial equation retains the literal remaining frame list and every unchanged field. The complete equation retains call view, result type, receipts and literal suffix, with the precise folded world/scopes and observed list.

`request_step_unique` is inversion restricted to requesting/requested heads, not global transition determinism. `request_prefix_rank` proves `n + requestRank t = requestRank s` along an actual prefix. Consequently `call_request_prefix_iff` quantifies over arbitrary `n` and derives its upper bound; it does not assume that bound. Realization is constructive frame induction using actual constructors. The partial equation covers any consumed/residual split. At exactly the original frame count the head is still requesting with no frames; the additional step completes. `call_request_completion_iff` proves both directions for any actual prefix, and `call_requested_no_step` rejects every outgoing represented transition. Totalization of `requestNext` outside requests does not add transitions or support a longer legal prefix.

For composition I inspected `CallFiniteTyping`, `CallPrefixTyping`, `CallStepTypingRepair`, `CallTerminalTyping`, `CallUnwindTypingRepair`, `CallCaptureTyping`, `CallResponseCancellation` and `CallCaptureResponse`. Initial typing is constructed from the existing typed Call term and independently typed literal suffix. The actual initial prefix is appended to the realized boundary segment; existing step/prefix preservation yields terminal typing and literal suffix equality. Terminal inversion supplies payload and captured-continuation typing. Instantiating `plugResponse_captureFrames_typed` with an empty outer frame list is valid: the entire already-captured continuation is its typed argument. The independently proved cancellation equation then transports typing to plugging the original frame list. `actual_call_request_completed_response` obtains exact length and endpoint from the actual post-prefix and applies that constructive result. Its response remains an explicit closed typed input.

The represented universal request-boundary and typed actual-request composition obligations are discharged by these artifacts, subject to primary adjudication. The original complete semantics/type-inference goal remains **OPEN**. No unrestricted Call progress, Force progress/realization, raw Call coverage, metadata authenticity, source/native response existence/correspondence, original Call/inference A/B or production closure follows. Existing represented typing premises, an actual prefix to the requesting state, typed suffix and typed supplied response remain explicit. Missing raw/source/native bridges remain with their recorded primary/source owners; this review introduces no source-domain restriction and approves no compiler slice.

## Frozen evidence

| Artifact | SHA-256 |
|---|---|
| `CallRequestBoundary.lean` | `28ffc2943c18d324c35dacf18b4dd70921d4cc462ffd6ffdce989475ef46cce6` |
| `CallRequestBoundaryComposition.lean` | `fed00f06cdbf2a5bdc1b3c18957acc33c7b281e890f277ca5bd1d20ece53ee76` |
| `.lake/call-request-boundary-r2-check.lean` | `8595e7b81d9a495604166380659a6474bb60737658f6625237f74e306498bbb3` |
| `20261025-call-request-boundary-r2-verification.jsonl` | `4df963ddb36e55246ef204a67f676633e26b2c0da3c4bb8782adcd8c7a53062d` |
| boundary `.olean` | `5d2a9cca1d2ace3e09c0ae67d58d49683d15f0cf53e52f10ccd0a86ab25cde54` |
| boundary `.ilean` | `3ee0022b0bedb57d6f4fef5ebd909e910060521ac337ddaa50b6c24edf3671e2` |
| composition `.olean` | `b6dc54fe44ba8fd1696f8a84baa9ccd221d7bef81b971a3b8caa81d0bb76e774` |
| composition `.ilean` | `deb40737f96df2227450ccdb7e921c862d8f33a9d7b73132eb7afaf59483bb13` |

Every r1 pinned dependency/toolchain-file hash matches the worktree. For final rows 2, 4 and 5, respectively all 17, 45 and 47 input hashes, their after snapshots, and every generated output hash match the current bytes, including the imported `.olean` files. Each of all five embedded source snapshots hashes to its recorded input source hash. Row 1 records the earlier successful boundary development source; row 3 honestly records the failed composition elaboration and missing outputs. Neither substitutes for final certification. Row 3's result-type unfolding repair is present in row 4. The final source/query sequence is chronologically ordered and serialized, with unchanged inputs during each recorded invocation.

Rows 2/4/5 exit 0 with empty stderr; source compilation rows have empty stdout. Row 5 contains all ten full public signatures and all ten axiom reports, each exactly `[propext]`, within the allowed `[propext, Quot.sound]` subset. The signatures retain arbitrary metadata/world and the advertised actual-prefix and typed-response premises. No `sorry`, `admit` or custom `axiom` declaration occurs in the inspected source import closure. Five recorded Lean invocations total `2.2030718979985977` seconds, all below the specified caps; the transcript has no timeout. These are inspected execution receipts, not an independent rerun or authentication of the producer's identity.

All 15 concrete query examples were inspected: forward and reverse noncommuting scope/view folds; their inequality; effect/result identity distinction; nested captured scope/expose syntax; mixed bind/adapter syntax and order inequality; the incorrect plain-successor binder alternative; response cancellation with an open body; the incorrect index-one response alternative; requesting at length three; requested at length four; original observed context and literal suffix at completion; rejection of the alternate observed list; and impossibility of a fifth actual step. They distinguish the named mutations while the general proofs supply universal coverage. Examples involving an arbitrary call view do not assert source authenticity or typing of the open witness state.

## Handoff and STOP

Review used three bounded stages: source/authority inspection; dependency, signature, falsifier and receipt comparison; this frozen report. Only this report was written. No Git mutation, other artifact edit, descendant spawn, external contact, Lean/test/build rerun or semantic/configuration change occurred. The initial `python` read-only inspection command was unavailable; the same inspection used `python3` successfully.

Writer state: **STOPPED upon this report's completed write**. No descendants, pending subprocesses or unresolved descendant leases exist. This report is frozen revision 1; primary owns adjudication, current-state reconciliation and integration. No further in-envelope work remains. Review completion timestamp is supplied by the report filesystem/write receipt; precise effective-model and scheduler telemetry remain UNKNOWN.
