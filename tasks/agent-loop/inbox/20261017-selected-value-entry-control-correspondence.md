# Selected Value-entry control correspondence handoff

Sprint-ID: `receive-checked-inlet-bridge-and-entry-control-20261017`  
Contract revision / SHA-256: **2** / `aaa610f373dea738ffeb9a34edbe4d1ae85bbd11b6f48a1e449b28d733889ee6`  
Assignment-ID / handoff revision: `F2-ENTRY-CONTROL-20261017` / **1**  
Parent Goal: `型推論と実行器が証明込みで実装できるまで続ける`; original theorem and production gates remain OPEN.  
Outcome class: **bounded HIR/runtime source control correspondence candidate**.

## Result and parent application

- Author/primary: `/root` (Luna/high), sole writer. Actual active-work receipt: 2026-10-17 03:05:18 UTC, after the proof author STOPPED and all 20 contract dependencies plus both frozen proof outputs rehashed MATCH. Requested gpt-6-luna/high; effective model/effort UNKNOWN. No descendants.
- Exact path: selected `my apply f = { my step x = f x; step }`, with the `step` closure's annotation-derived Value entry. Runtime allocates an inert whole-argument Delay, pushes ValueEntry before executing it, and binds the same formal only after actual Return. A Request during Force unwinds the unfinished suffix including ValueEntry. A continuation-bearing handler stores/restores that frame; a non-resuming handler abandons it; an unhandled request stops with a continuation handle retaining the suffix.
- This matches the control **order** of the selected `Strict(I_x,x:A_x,R_c,IF_step)` Value-entry phases under its independent admission, result/rebind, pending and resumption premises. It does not prove full typed-view simulation, every semantic descriptor observation, runtime execution, source `T`, MODEL, or original F2 admission. Value/Computation does not infer Pure/Handler.
- The earlier HIR trace rev3 supplies the identity join: closure/formal ID and captured environment survive creation, local return/alias and lookup. This control trace adds the timing and continuation order; no candidate fresh-use transport is needed for this selected runtime-only classification. Generalization to other consumers remains OPEN.
- The first missing join for full erasure is typed evidence: no source law maps original `I_x`/`B_in` domains and all typed pending/return observations onto the runtime Delay view and transitions. The actual control order shows no counterexample on this selected path. Both original F2 VIEW and CHECK remain OPEN, and no source-qualified c2 counterexample is claimed.
- `NO_SAFE_CODE_SLICE`: runtime already preserves entry, rebind and unfinished-suffix order. The absent dependency is the original source-owned admission/typing law. No code, tests, builds, probes, execution or expected-output changes were authorized or made.

## Source locators

- Formal annotation and role: `tools/inference-playground/src/runtime/program.rs:382-402`.
- Delay creation and selected Value/Computation dispatch: `runtime/machine.rs:661-747`; Delay execution `:1581-1586`.
- Actual result rebind before body: `runtime/machine.rs:819-836`.
- Request creation/unwind: `runtime/machine.rs:1587-1606,1235-1413`; no-continuation suffix abandonment `:1295-1357`; unhandled suffix retention `:1415-1427`.
- Continuation capture/call/response/restore: `runtime/machine.rs:1013-1082,575-601,680-691,1104-1107`; immutable node shape `runtime/continuation.rs:13-44`.
- Delay view inheritance only: `runtime/receiving.rs:114-129`; this is not a full original inlet interpretation.

Artifact: `notes/theory/2026-10-17-selected-value-entry-control-correspondence.md`  
Artifact SHA-256: `3a3af2183ce9962ae0e77eb33c91271d69fb8bb88c12229e42424ea7f2d50472`  
Handoff: this file; SHA-256 is computed after this write and recorded in current state/review target.

Five runtime owners plus both proof outputs were pinned and rehashed at lane entry and matched at freeze. The artifact carries the exact source hashes. Checks were static source reads, control-stack tracing and SHA-256 only. No test/build/probe/runtime execution/Git, no scratch outputs. Luna stopped writing on freeze; no unresolved descendants.

Resource: active-work 2026-10-17 03:05:18 UTC; freeze 03:08:26 UTC; 188 seconds elapsed, conservatively **240/480 seconds charged**, 240 unused and retired. This source budget is separate from the proof lane's 420/720 seconds; total sprint charged so far 660/1800. Independent compiler-referee, spec-auditor and architect reviews are pending; this is not self-certification or gate closure.
