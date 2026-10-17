# Static instance of proposed Catch target declarations

Status: provisional source/native correspondence for a Draft rule; no semantic
adoption, compiler edit, execution, accepted-source claim or production status.
Author: Luna primary `/root`, within sprint
`catch-matcher-target-declaration-20261017`, revision 1. Contract SHA-256
`ccb332b41ae50c5361a977bbe6ba9791c5854123c3a20958e70a732ab5262170`.

## Fixed specimen and source declaration fields

The pinned specimen is 138 bytes, with operation `ping: () -> (int -> int)` and
body `catch (signal::ping())(1) { signal::ping(), k -> k id, v -> v }`. The
prior exact-source receipt says its candidate HIR had `UnsupportedItem` and
`UnsupportedExpression`; this note makes no claim of complete HIR acceptance.

At the proposed outside matcher occurrence, the declaration maps these
interfaces separately:

| Field | Proposed source declaration | Existing producer/consumer evidence | First missing join |
| --- | --- | --- | --- |
| Event metadata `q` | `InspectRequest_μ` eliminates the exact historical Event telescope at its original `C_y,J_y` indices; it does not make q a value | Original Request clause carries q to μ_H; runtime checks the request declaration while `CatchReturn` is still top | No source-native certificate equates that pre-pop runtime check with the proposed outside post-exit metadata read |
| Payload `P` | `PayloadAt_μ(q)` retains the declared operation argument schema and binds the same payload under the introduced target schema | `candidate_catch_operation` derives both polarities from the operation argument and connects them through occurrence slots 60/61; runtime later binds `ReceivedValue` after Catch pop | No current source binder/slot action, typed target view or complete evidence-root correspondence is present in those native constraints/binding cells |
| Response entry `B` | The raw telescope retains the operation result interface and each original admitted response tuple `τ`, including provider and `Future(r)` | `candidate_catch_operation` derives the continuation's response ports from the operation result (slots 62/63); `ResumeArgument` checks the response on entry | No complete source descriptor or all-response admission/preservation witness is attached to the runtime continuation view |
| Suffix answer `A_S` | Owned by the complete saved suffix at its answer cut, before caller continuation `a`; carries actual returned provider, output evidence and future | `candidate_catch_operation` derives answer ports from the original scrutinee endpoint; `ResumeReturn` returns the actual suffix result | The candidate scalar Function ports do not include complete S, output-history or dependent answer/future typing |
| Raw/captured state | `RawAt_μ` passes the same raw handle; `BindRaw` declares `e_saved`, ordered suffix S and the B→A_S callable body | `capture_template` retains saved nodes/declaration/original event; `receiving::opaque` has `image=None, unknown=true` | No complete typed raw-view certificate, source binder action, or correspondence from captured template to the proposed dependent telescope |

For this specimen, the visible skeleton is:

```text
P = Unit
B = Int -> Int
S = ApplyOne(r) = Call(r, 1)
A_S = Int
k : B -> A_S       -- skeleton only; the proposal's full dependent telescope is larger
```

This rules out reading k as merely `B -> B`: the saved suffix applies the
received B value to `1` and returns its A answer. It also rules out replacing
the complete S answer by B merely because both contain a function in the
response path. These are field correspondences, not accepted-program typing.

## Source/native owner correspondence

The candidate owner sequence is:

```text
Builder::catch
  -> Work::CatchArms
  -> Action::CatchOperation
  -> candidate_catch_operation
  -> generated value/effect constraints
```

The inspected source note identifies the existing HIR/candidate identities,
original scrutinee endpoint and arm binders. `candidate_catch_operation`
uses the operation declaration's argument schema for payload ports and its
result schema for B, while it uses the original scrutinee endpoint for A. Its
entry/full-scrutinee effect constraints (slots 64/65) remain distinct from
those value ports. These constraints do not create the new source
`InspectRequest_μ`, a complete Δ_q, S, current owner/slot action, or a typed
raw view. Existing scalar connectivity is not a source typing derivation.

The runtime chain has a different phase boundary:

```text
propagate_request:
  inspect request declaration / local grant / payload / response tag
  capture_template(request, ...)
  pop CatchReturn
  bind payload and opaque continuation outside
ResumeArgument: check operation response B
ResumeReturn: return the saved suffix answer A_S
```

The known Function-response guard rejects the specimen at the pre-pop result
check because the declared operation result is Function-shaped. This is carried
forward only as the already recorded conditional playground limitation; it
was not rerun. Nothing here claims that a post-pop Function continuation binds
or that source compilation accepts the specimen. The operation response and
saved suffix answer remain distinct even in this refusal path.

## Application and stop boundary

The concrete equations instantiate §§3–5 of the frozen Draft: metadata has
only historical dependencies, payload's map is scoped to its declared
operation-argument schema, and raw retains response B plus answer A_S and the
captured suffix. They point toward prospective MI-Intro fields 7 and 14–15,
but the native producer/consumer chain lacks the declaration and dependent
certificates those fields need. The proposed local metadata preservation does
not prove native correspondence.

No complete `M_exit` follows. Full raw preservation still requires actual
OriginalFrame bodies, every original response admission, current world/owner
resolution, provider and output-future actions, complete binder/Receive maps,
and the actual S answer cut. General pattern, NoArm, mismatch, false/effectful
guard, suspension and FK1 foreign-continuation cases remain open. The
Function-response guard remains in place. No code slice is authorized by this
static instance; the next implementation step needs adoption of the target
rule and a new exact code lease.

No tests, builds, runtime, compiler execution, probes, fixture/expectation
edits, or outside dependencies were used. Static source reads only. The
conditional source lane used about 90 seconds of its 300-second cap; exact CPU
and memory unmeasured. Author writes stop at the paired frozen handoff.
