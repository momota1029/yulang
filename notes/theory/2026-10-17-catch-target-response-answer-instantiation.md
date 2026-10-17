# Static instance of proposed Catch target declarations

Status: provisional source/native correspondence for a Draft rule; no semantic
adoption, compiler edit, execution, accepted-source claim or production status.
Author: Luna primary `/root`, sprint
`catch-matcher-target-declaration-20261017`, instance revision 2.
Contract SHA-256:
`ccb332b41ae50c5361a977bbe6ba9791c5854123c3a20958e70a732ab5262170`.

Revision 2 corrects one major review finding against revision 1. In the fixed
specimen, the operation pattern `signal::ping()` has a Unit payload pattern,
not a payload variable binder. Therefore `payload=None` reaches
`candidate_catch_operation`; its optional payload branch and slots 60/61 are
skipped. The runtime Unit pattern leaves the environment unchanged. The
payload value shape remains `P=Unit`, but this specimen supplies no variable
payload use, no candidate payload-link evidence and no runtime payload bind.
Revision 1 bytes remain preserved in Git history at the previously reviewed
snapshot; no proof proposal bytes or source semantics changed.

## Fixed specimen and operand ownership

The prior pinned source receipt identifies the exact 138-byte specimen:

```yu
act signal:
    our ping: () -> (int -> int)

my id x = x; my result:int = catch (signal::ping())(1) { signal::ping(), k -> k id, v -> v }
```

The receipt records `UnsupportedItem` and `UnsupportedExpression` in partial
HIR. This note makes no claim of complete HIR acceptance. The target rule
proposal and static source receipt distinguish these fields:

| Field | Proposed declaration | Exact specimen evidence | First missing join |
| --- | --- | --- | --- |
| Event metadata `q` | `InspectRequest_μ` eliminates the exact historical Event telescope at original `C_y,J_y` indices; it does not make q a value | Original Request clause carries q to μ_H; runtime reads declaration metadata while `CatchReturn` is still top | No source-native certificate equates that pre-pop runtime read with the proposed outside post-exit metadata read |
| Payload `P` | `PayloadAt_μ(q)` declares the operation argument schema. `BindPayload` is conditional on an actual variable pattern | `P=Unit`; the exact empty-call pattern lowers to Unit, `Work::CatchArms` supplies `payload=None`, and runtime Unit handling does not bind | This specimen has no payload variable use or candidate slots 60/61. Generic variable-pattern correspondence needs its own actual binder/slot premises |
| Response entry `B` | Raw telescope retains operation result interface and original admitted response tuple `τ`, including provider and `Future(r)` | For a continuation binder, `candidate_catch_operation` derives response ports from the operation result (slots 62/63); `ResumeArgument` consumes/checks B | No complete source descriptor or all-response admission/preservation witness is attached to the opaque runtime view; the Function-response specimen branch is refused before capture |
| Suffix answer `A_S` | Owned by the whole saved suffix at its answer cut, before caller continuation `a`; carries actual returned provider, output evidence and future | Candidate continuation answer ports derive from original scrutinee endpoint; `ResumeReturn` returns actual suffix result | Scalar Function ports do not include complete S, output-history or dependent answer/future typing |
| Raw/captured state | `RawAt_μ` passes the same raw handle; `BindRaw` declares `e_saved`, ordered suffix S and B→A_S callable body | `capture_template` retains saved nodes/declaration/original event when reached; `receiving::opaque` stores `image=None, unknown=true` | No complete typed raw-view certificate, source binder action, or correspondence from captured template to the proposed dependent telescope |

The visible skeleton is:

```text
P = Unit                         -- exact Unit pattern, no binder
B = Int -> Int                   -- operation response entry
S = ApplyOne(r) = Call(r, 1)
A_S = Int                         -- answer after the entire saved suffix
k : B -> A_S                     -- skeleton only; full telescope is larger
```

This rejects treating k as merely `B -> B`: the saved suffix applies the
received B value to `1` and returns its A answer. It also rejects replacing
the S answer by B. These are field correspondences, not accepted-program
typing or proof that this exact Function-response path executes.

## Source/native correspondence

The candidate owner sequence is:

```text
Builder::catch
  -> Work::CatchArms
  -> Action::CatchOperation
  -> candidate_catch_operation
  -> generated value/effect constraints
```

For the exact Unit pattern, the HIR/candidate source passes `None` for the
optional payload endpoint. Consequently the producer does not enter the
argument-link block and does not create slots 60/61. If an operation arm has an
actual payload variable pattern, that separate conditional branch derives
both payload polarities from the operation argument declaration and links
slots 60/61; the fixed specimen is not evidence for that branch.

The continuation binder is present in the specimen's parsed form. Its
conditional candidate branch derives B from the operation result and A_S from
the original scrutinee endpoint; slots 62/63 connect the Function value ports.
Slots 64/65 keep entry and original-scrutinee effect constraints separate.
These candidate constraints exist independently of a runtime execution, but
they do not create `InspectRequest_μ`, a complete Δ_q/S certificate, current
owner/slot actions, or a typed raw view. They remain scalar/native evidence,
not complete source typing.

The runtime chain is statically ordered as:

```text
propagate_request:
  inspect request declaration / local grant / payload / response tag
  capture_template(request, ...) when the binder branch reaches it
  pop CatchReturn
  Unit pattern: leave environment unchanged
  variable payload pattern: bind payload after pop (not this specimen)
  bind continuation wrapper after pop when reached
ResumeArgument: check operation response B
ResumeReturn: return the saved suffix answer A_S
```

The operation result in the specimen is Function-shaped; the known runtime
guard rejects it before capture/pop. This is carried forward only as the prior
conditional playground limitation and was not rerun. Nothing here claims a
post-pop Function continuation binds, or that source compilation accepts the
specimen. The B/A distinction holds at the declared source and candidate
interfaces even though this runtime branch refuses before its consumer path.

## Parent application and remaining evidence

The corrected instance supports the proposed field separation: metadata has
only historical dependencies; payload is a Unit-pattern case with no binder;
raw retains response B, answer A_S and the captured suffix. It points toward
prospective MI-Intro fields 7 and 14–15 but provides no complete `M_exit`.

For this specimen, the actual missing source/native join is the source-owned
outside `InspectRequest_μ` and raw continuation declaration/certificate: the
runtime metadata check occurs before Catch pop; the proposed read is after the
original exit; payload's Unit match supplies no variable binder; and the
Function-response runtime branch does not reach raw binding. Full raw
preservation also needs actual OriginalFrame bodies, every original response
admission, current world/owner resolution, provider and output-future actions,
complete binder/Receive maps and the actual S answer cut. General pattern,
NoArm, mismatch, false/effectful guard, suspension and FK1 foreign-continuation
cases remain open.

No tests, builds, runtime, compiler execution, probes, fixture/expectation
edits, network or new dependencies were used. Static source reads and review-
delta correction only. Correction charge is within the selector-authorized
120-second repair slice; exact wall span is recorded in the compact current
snapshot. No code slice follows. Any implementation needs semantic adoption
of the source rule and a new exact lease.
