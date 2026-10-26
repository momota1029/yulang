# Primary intake and rejection preservation — SOURCE-RELAY-RETURN-INSTANCE-20261026/r1

Status: IN PROGRESS; this receipt records rejected bytes, not accepted source proof.
Contract SHA-256 `cb69afdf901bd1fbb0a5838da6af46ef55de50609c345e61cec144b19da9396f`.
Baseline `cc99471f36b167a8cfd526c5853f1c12077aaf58`.

## Source r1 disposition

Primary REJECTS source candidate r1. The explicit `thunk:[] (int -> int)`
formal has retained Computation entry; it is not Value entry. The body Result
consumes C and produces W. This invalidates the claimed relay Value-entry
identity spine, same-binding result argument, and claimed ReturnView/FL12
instantiation. Actual RootCompReturn closes C's execution and preserves W;
there is no ground-result rewrite. A syntactic owner path does not construct T.
Source worker acknowledges each finding after supported interruption and
returns STOPPED/no descendants or child processes. Its1200 active seconds are
UNKNOWN, conservatively unavailable for further work; no budget reset.

Rejected source note SHA-256:
`b7a7617261d3b29ea844cdf0a2e1407203f381f86597be50dd2b4845df00ea4c`.
Frozen original handoff remains verbatim at
`tasks/agent-loop/inbox/source-relay-return-instance-20261026.md`, SHA-256
`050d3b16baada7114aaf5e822802f88e813fd8a9649ee77549d6d058496ae1fc`.
Its self-reported STOPPED was not sufficient until actual runtime cancellation
and the subsequent explicit cessation receipt; no lease was reclaimed earlier.

The exact rejected note bytes can be reconstructed as UTF-8 text inside the
following fence, including its final newline. They are retained only as failure
evidence; every claim below is superseded by the primary rejection above.

````markdown
# Source relay return instance: constructor ledger

Status: bounded source-owner construction candidate; fresh non-author review
pending. This is not an independently certified derivation or production
authorization.

## Fixed instance and notation

The source is the existing `machine.rs` fixture at occurrence site represented
by the exact text

```yulang
my relay (thunk:[] (int -> int)) = thunk
my main = relay (\x -> x)
```

Use the original binding identities `r` for `relay`, `t` for its `thunk`
formal, `m` for `main`, and `x` for the lambda formal. Let `xi=(nu,K,D)` be
the one original joint assignment, with the original scopes and source
instances. `C` is the actual computation consumed by the `relay` Call;
`C.result` is the result edge of that same `C`; `W` is the actual packet
returned by that execution. No assignment is replaced by a fresh marginal
witness.

## Actual constructor derivation, before semantic membership

The source tree fixes the following constructor spine, using the selected
Source-Generalize rules and typed-core meanings:

1. **Parameter(t).** The written outer `[]` is attached to the original
   formal `t`, and the written Function value interface is `(int -> int)`.
   Parameter installs the source entry role and the formal binding at its
   original scope. The annotation is an operand for this constructor, not a
   proof that a callable profile or a return-path law holds.
2. **Name(t).** The body occurrence resolves to that exact formal. Its result
   is the actual bound value/provider under the same `xi`; the body does not
   synthesize a new callable. This is the identity return used below.
3. **Result(Name(t)).** Result returns that same value and current-world
   witness. There is no conversion node or second producer between the Name
   and Result. Thus the Result value correspondence `mu` is identity on this
   actual value; it is not inferred from equal Function shapes.
4. **Lambda(r).** The `relay` Lambda owns Parameter(t), the Name/Result body,
   its actual entry and its complete invocation. The source entry of this
   Value formal is the ordinary force/rebind entry. For each admitted carrier
   challenge `d`, the entry sequence is `Force(d)`; on an actual Return it
   rebinds the returned value at the resulting current world; the body Name
   then reads that rebound value and Result returns it. If Force requests,
   the original pending suffix is retained and resumed at the actual resumed
   world; the sequence is not restarted and no Return witness is fabricated.
5. **Lambda(x), Name(x), Result.** The argument occurrence is a Lambda with
   its own Value formal `x` and identity body. Its selected `int -> int`
   view is represented by the source Lambda's own entry/body/result
   derivation. At each admitted argument challenge, its Value entry forces
   that challenge, rebinds the actual returned integer and its current world,
   then its Name/Result body returns that exact rebound integer. The Function
   argument itself is not run while forming the enclosing Call's inert whole
   argument.
6. **Delay(argument).** The Call retains the entire Lambda value as the
   delayed argument carrier at the original argument slot. Delay formation
   and designated execution remain separate obligations. This derivation
   identifies the original slot and carrier; it does not infer a closure
   profile from the carrier's runtime tag.
7. **Call(Name(r), Delay(Lambda(x))).** The callee is the actual `relay`
   binding. Call uses its actual returned callee, receiver, receipt, entry,
   designated result consumer and invocation return. The invocation return
   supplies the same `W` and same current-world witness used by Result(Name(t))
   above. The complete-call consumer is the `relay` provider's complete
   `ExecuteCallable` consumer, not a second invocation of `relay`.

This is a source-rule derivation spine for the fixture. It does **not** by
itself prove the independent contextual Function-membership judgment needed
to admit either Lambda as a callable. In particular, it does not take `T`,
body safety, callee acceptance, `LocalLaws`, `CallableExport` validity or the
desired result export as a premise.

## Identity callable obligation: what the entry construction proves

For `relay`, the local execution equation is fixed by its actual Value-entry
Lambda and Name/Result body:

```text
actual challenge carrier d
  -- Force at relay's Value entry --> (a, world1)
  -- rebind t := Value(a) at world1
  -- Name(t); Result --> (same a, same world1)
```

This establishes the producer-side same-value fact for every execution which
reaches that entry Return. It also handles every finite request/resume prefix:
each request retains the original entry/rebind/body/return suffix, each
resumption uses its own actual current world, and only a reached Return fills
the dependent result binder. It makes no claim that every admitted `d`
terminates or returns. For a nonreturning finite prefix there is no `W` to
project; the original pending/divergent behavior remains in the challenge.

The remaining contextual-membership premises are not discharged merely by
this local identity equation. The challenge context/domain and its complete
carrier admission must be the independently formed ones from the selected
contextual-membership definition. Membership still needs the full acceptance
and observation obligations at the actual provider/receiver and under the
whole `xi`, including request/resume observations, hard envelope, scopes and
receiver correlation. The fixture supplies no concrete inhabitants for every
such independently admitted challenge. This is therefore a real partial
constructor proof, not a proof of universal Function membership.

For `\x -> x`, the same local identity equation holds at the actual `Int`
formal and its Result. The annotation/result target fixes the displayed
`int -> int` view, but that shape does not construct its complete challenge
domain or prove its own contextual membership. A pure-row instance can account
for only executions whose actual observations satisfy that independently
fixed pure contract; it cannot erase an effectful admitted prefix by calling
it vacuous. The source premises available here do not establish that all
independently admitted `Int` challenges are pure or terminating.

## Same-execution ReturnView and complete Call consumer

Apply the reviewed result projection to the one execution above, with the
actual `C`, `W`, and source instances just identified:

```text
rho_C(C.result.q) = q              for each actual result path q
rho_C(C.effect)   = undefined
ReturnView(C,W) = mu*W union_tagged rho_C*V_C
mu = identity for this Name/Result return
```

The effect position is excluded from this result image. This does not delete
an independently sourced incidence of the same boundary already on `W`.
`W` is produced by this execution, not an independently chosen packet. Its
actual current-world witness and original provider/receiver IDs remain tied
to the same `nu,K,D`, source instance and scopes. Unknown result coverage
retains the original result-indexed dependency; it is neither made globally
present nor silently declared empty.

The later complete consumer is the actual Call of the returned callable: its
`ExecuteCallable` observation runs under the transported `ReturnView` at the
original complete-call port and current receiver. The designated consumer
spans the actual producer's entry, body and Result; it is not a generic
Function-shape observation. This instantiates the reviewed ReturnView/FL12
consumer route for the fixture's owner path, conditional on the source
membership and profile-supply premises explicitly listed below. No native
code is claimed to generate or store this source object.

## Premise ledger

| Original premise | Actual constructor/evidence in this fixture | Status |
|---|---|---|
| Authentic source occurrences, lexical scopes, bindings and instances | `relay`, `thunk`, `main`, lambda formal `x`; resolved Name is the body `thunk` or `x` occurrence | fixed syntactic constructor data; full raw-HIR-to-judgment bridge remains open |
| Parameter role and annotation operands | Parameter(t) and Parameter(x), with their source annotations / inferred value endpoint | constructor operands identified; annotation realization to complete applicable profiles is not established by syntax |
| Name binding preservation | Name(t) / Name(x) read the actual binding at current world | constructor equation supplies identity; hereditary membership still depends on binding certificate |
| Lambda entry and complete invocation | actual Value entry, Force, Return/rebind, body, Result and invocation return | operational/source equation supplies local shape; universal challenge acceptance/observation remains open |
| Delay inert formation and designated execution | exact delayed Lambda argument at Call argument slot | slot identified; independent license/profile realization remains open |
| Call's actual callee, receiver, receipt and consumer | Call(Name(r), Delay(Lambda(x))) and relay's complete callable consumer | constructor route identified; actual compatible receiver/context inhabitants and source/native join remain open |
| Actual returned packet `W` and current world | only an actual Return through relay's invocation fills these | same-execution dependent witness; absent on nonreturning/pending prefixes until Return |
| Result edge and prefix removal | exact `C.result` at this consumption; `rho_C` from reviewed projection | reusable generic source theorem applied; source producer must still supply its full typed paths |
| Independent returned-value packet `W` | actual Result(Name(t)) packet, identity `mu` | source rule gives same-value return; contextual profile contents remain unsupplied |
| Full `xi=(nu,K,D)`, scopes, provider/receiver correlation | retained as the single original assignment and source binders | no marginalization; concrete assignment contents are arbitrary only where the original premise quantifies universally |
| Pure-row/vacuity case | `[]` is the fixed written row in the fixture's formal annotation | does not imply empty challenge domain, termination or absence of pending prefixes |
| Nested-effect discriminator | none constructed from the supplied source instance | no source-specific counterexample claimed; first missing item is independent annotation/profile realization for a nested effect path and its authentic challenge/consumer premises |

## First source-specific gap and falsifier

The first unavailable constructor premise is the independent realization of
the annotation's complete callable profile and contextual challenge domain at
the actual Parameter/Lambda owners. Existing annotation coordinates and a
native Function pointer equality are not that realization. To close this
gap, evidence must exhibit, from the selected original source/interface
constructors, the actual complete challenge set, whole carrier admission,
provider/receiver and world correlations, and the body/consumer observation
proof for each admitted challenge. If any admitted challenge reaches a
requesting Force, its same pending suffix and resumed current world must be
shown; if it never returns, it cannot be used as a returned `W`.

The falsifier is direct: an alleged derivation that obtains universal
membership by assuming the same body-safety/callee-acceptance conclusion, or
that infers the profile solely from `(int -> int)`/native pointer shape, is
circular and fails before ResultView extraction. An alleged pure-row proof
that drops a possible admitted effectful challenge also fails at this first
membership premise. This is an exact unclosed premise, not a constructed
counterexample.

## Native/source correspondence boundary

The previously reviewed native producer/consumer equations can be joined to
the source owners only as owner correspondences: Parameter/entry maps to the
actual Value entry; Name/Result maps to actual binding/read/return; Call maps
to the existing complete `ExecuteCallable` consumer. The pinned runtime's
ground-result rewrite and later Function consumer obstruction remain as
previously reviewed. This source derivation does not show that inference or
HIR produces the whole `T`, that runtime carries `rho_C`, or that a returned
Function profile reaches that consumer. Rust remains `NO_SAFE_CODE_SLICE`.

No nested-effect source instance was constructed: the independently realized
annotation/profile/challenge premise above is the first missing constructor
input. No unbuilt nested case is called a counterexample.
````

## Corrected r2 intake and frozen review target

Source-note r2 SHA-256 `b8d806d2768cc1231ca4361ebe221190fde3f988f0c3ca7f41edc868e52afdbf`. Primary took its exact lease only
after the source worker's explicit cessation, preserving rejected r1 above.
Original source handoff remains byte-identical. Current corrected source was
constructed by primary; the source worker and dispatcher are not independent
reviewers. Source r1 and corrected r2 are not a proof of T.

The existing dispatcher was consulted once at the material rejection/source-to-proof
seam and recommended correcting retained entry and reviewing the exact missing
Lambda premise. Primary accepts this routing. Proof allocation1500 remains
NOT_ISSUED, zero checker calls; an independent admitted challenge must be handled
abstractly, not enumerated. Corrected source identifies the actual absent W Call
in the fixture and leaves a genuine future-context consumer unconstructed.

## Static and environment evidence

All31 exact contract pins independently revalidated against both working bytes
and baseline Git. Contract SHA-256 remains
`cb69afdf901bd1fbb0a5838da6af46ef55de50609c345e61cec144b19da9396f`.
Supplemental selected semantic-input source hash
`fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a`
also equals baseline Git. No governing source changed.

Both `/tmp/yulang-source-relay-return-20261026/{proof,primary}` snapshots
contain the141 tracked baseline project files, initially verified byte-for-byte
against the pinned commit. Initial archive preparation failed on an overstrict
path-prefix assertion because Git archive includes directory `notes`; no file
was extracted. The repair checked the exact regular-file set, path safety and
absence of symlinks before extracting into the known empty/new owned directories.
This was static preparation failure, not a Lean failure.

Only primary's leased `run_call.py` was prepared. Neither owner ran a version,
build, probe or audit; no Lean candidate/root import/build output was created.
No new theorem/type/axiom audit exists for this sprint. A later attempted
source correction via apply_patch failed because delete/add targeted one path;
no source mutation occurred in that failed call. A direct whole-file write
then produced the corrected r2 bytes above. A read of guessed `SourceProblem.lean`
failed; the actual abstract declarations were inspected in `Contracts.lean`.
These static failures are not mathematical counterexamples.

No tests, Cargo, runtime probes, network operations, compiler edits or
dependency changes. Root active seconds were not instrumented across context
continuation; actual usage UNKNOWN, no budget reset or invented compliance
measurement. Source1200 is conservatively charged in full; checker usage is
exactly0/6 and0/360s for both owners. Proof1500 remains unused and unrenewed.

## Review boundary

Freeze this receipt and corrected source for one fresh non-author compiler
referee,420s/read-only/zero checker/no descendants. Review checks the retained
entry and C/W correction, absence of an actual later W Call, exact first
unfilled constructor premise and prior results' limits. It must not certify
T from this note. Final adjudication, review hash and Git outcome belong in
the sprint outcome, not a rewrite of these frozen evidence bytes.
