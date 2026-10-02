# Ordinary source computation semantics: milestone package

Date: 2026-10-02
Status: Draft; coherent candidate source rules; adequacy and principality unproved; not implementation authority
Scope: calls, closures, thunk force, operation requests, callback boundaries,
and shallow handlers for the ordinary effect sublanguage
Supersedes: none
Inputs: user-selected soundness/principality priority, unified-relation
requirement, nested-capture preservation, ordinary escaped-callback handling,
and symbolic typed-family transport
Primitive/derived review: compiler_referee and spec_auditor, 2026-10-02; no findings in charter §15's outside shallow selection and explicit deep expansion
Invocation review: compiler_referee and spec_auditor, 2026-10-02; common entry expansion reviewed; operation-payload gap repaired and closed by independent compiler_referee delta

## 1. Milestone claim

This package gathers the existing local evidence into one source-machine
candidate. Its central choice is that a handler tests an event at the actual
configuration reached by ordered search. Ordinary visibility follows the
current active source configuration: a handler can handle an exact covered
operation when ordered search reaches it, subject to source-defined active
boundaries. No boundary belonging to an exited maker activation is carried
forward as a mask. Callback capture is the narrower contract relation used
when a request observation is connected by typed value flow and receiving
ownership to an active receiver-local candidate; handler ownership alone does
not require capture. It is not a property of an operation family or a value's
historical maker.

Under this choice, normal return ends the receiver and its handler
activations. A returned closure keeps its latent computation, event origins,
symbolic typed-family predicates, and required runtime lineage. Its later
application runs under the caller's current configuration. A fresh caller
handler may handle a request when ordinary search and the current boundary
relation admit it. No maker boundary remains as a persistent mask.

The ordinary-flow / escaped-callback consequence follows from the current
configuration rule below: normal return removes the maker's activations, and
later search uses only the caller's active ordered handlers and their
source-defined boundaries. The selected preservation rule also keeps a
receiver's already-derived concrete capture incidence available through nested
transitions in its callback's complete call/adaptation/force view while that receiver and handler remain
active. Source/interface adequacy, finite principality, and intrusion
preservation remain unproved milestones.

## 2. Complete configurations and requests

Fix one complete type assignment `ν` throughout an execution derivation. A
machine configuration contains:

```text
C = (expression, lexical environment, live store, ordered activations,
     value-carried runtime lineage)
```

Ordered activations contain the active call/receiver and handler frames needed
by source execution. Handler frames have a fresh dynamic activation identity,
the exact operations they implement, and their source position. Callback
receiver information is derived from the ordinary call/value derivation and
the contract at that call boundary; it is not a second handler stack or a
family-level flag. Runtime identities remain distinct from type binders in
`ν`.

A dynamic request event is represented at fixed `ν` by

```text
q = (operation, payload, origin, event, Kq, Dq, continuation)
```

`origin` identifies the source computation/value flow that produced or
exposed the request. `event` distinguishes repeated dynamic occurrences.
`Kq` contains the symbolic typed-family predicates for the operation and its
arguments/results; `Dq` records every root, residual, value, or continuation
view still constrained by those predicates. The pair `(Kq,Dq)` stays in the
same assignment `ν`. Event/origin labels are proof indices; type-family
equality alone never merges request histories.

The execution relation observes `Return(v,C)` and `Request(q,C,k)`, along
with every finite request prefix of a diverging computation. A request
continuation receives the actual response and live resumed state. Sequencing
is state-threaded continuation bind:

```text
Return(v,C) >>= F       = F(v,C)
Request(q,C,k) >>= F    = Request(q,C, λr. k(r) >>= F)
```

The second equation preserves the raw resumption and appends the continuation
to every resumption. It neither snapshots nor restores the store. This is the
single composition operation for ordinary sequencing, callbacks, adapters,
and delayed computations.

## 3. Calls, closures, delayed values, and requests

Effectful computations are first-class source data. Their introduction is
inert, and their execution begins only through explicit receiver elimination
(`Force` or handling), including the declared entry expansion below.
Construction is not a phase allowed to execute a prefix of that computation.

Application obtains the callee and reifies the **entire argument expression**
without executing any part of it. The user's source-reference clarification
(charter §§16–17; scheduling choice A) makes every function a computation
receiver. Value-parameter forcing belongs to entry in that same invocation.
Let `ArgumentCode(e₂,η)` be the code for the complete argument computation
with its lexical typed-value references; construction of `Delay` runs none of
that code. The application rule is:

```text
Runν(e₁ e₂,C) =
  Runν(e₁,C) >>= λ(f,C₁).
  let t = Delay(ArgumentCode(e₂,η_argument), lexical lineage) in
  ApplyValueν(f,t,C₁)
```

`η_argument` is the lexical environment at the application site; mutable
locations are retained by reference. Callee evaluation supplies the current
store and active configuration `C₁`. Reification does not snapshot either.
There is no carrier-construction execution prefix before `ApplyValue`.
`ArgumentCode` is the code represented by the introduced computation. Its
result may itself be computation data; neither lookup of such data nor the
result shape inserts another force. Any elimination within the code must
come from a source consumer. Its raw-source derivation is addressed by the
source-computation-role elaboration gate; this equation fixes introduction
and invocation order rather than pretending that derivation is already
available. In particular there is no implicit caller-side `CompleteResult`
force after `ApplyValue` merely because it returns an operation carrier.

Applying a closure evaluates its body in the closure's lexical environment
with the current caller's live store and ordered active source activations:

```text
ApplyValueν(Closure(entry;body,ηcl,L),t,Cnow)
  = Runν(entry;body,ηcl[t],Cbody) >>= ReturnFromInvocation
```

`Cbody` retains `Cnow`'s live store and active activation sequence, replaces
the expression and lexical environment by `entry;body` and `ηcl[t]`, and pushes
only the current invocation's fresh call frame. On normal return,
`ReturnFromInvocation` pops that invocation frame and retains the resulting
live store. A request suspension retains an invocation re-entry wrapper in
its continuation. Handler search may unwind the active occurrence of that
call frame; on resumption the wrapper installs a fresh/resumed occurrence
before running the saved source suffix and its `ReturnFromInvocation`.
Normal completion removes exactly that resumed occurrence. Re-entry threads
the actual live resumed store and required lineage; it never reinstalls the
consumed shallow handler or any exited maker receiver or handler activation.
This is ordinary invocation/continuation composition, not a new source
construct or callback-specific rule. `L` and inherited request origins are
preserved as proof/runtime lineage, not as an activation snapshot: lineage
alone neither implements invocation re-entry nor grants handler eligibility
or creates a blocking mask. An
already-derived capture incidence is transported through this transition
only while its same receiver and handler remain active.

The source boundary instances and typed receipt of `t` are established in
that invocation before its entry code runs. A computation parameter binds
the received carrier for the body, executing none of its argument if unused.
The statically known parameter interface determines demand; unknown portions
do not license speculative execution. A value parameter has the entry expansion

```text
Force(t) >>= lambda (v,C1).
  RebindResultPath(t,v,C1);
  Run(body, eta_cl[x := v], C1)
```

`RebindResultPath` abbreviates the existing typed-path transport and receipt
relation; it creates no new capture contract or boundary identity. The entry
force executes in its corresponding typed computation view within the
complete call view. Its result `v` is kept as a value, including a latent
function/thunk result. This is one source activation with an entry program,
not a call to a synthetic wrapper function. No implicit operation arm is
created by treating every function as a handler/computation receiver.

If entry force yields a request, its continuation contains rebinding, body
and `ReturnFromInvocation`. The ordinary bind and owner re-entry rules below
retain that suffix on raw resumption without restarting entry or reviving
old grants. Entry effects therefore contribute to the complete invocation
even when the body is pure. Source-computation-role §10 gives the expansion
law; moving this force before invocation is a separate optimization theorem.

The explicit occurrence protocol is developed in
`2026-10-02-typed-source-owner-realization.md`, §2. Saved source owner spans
cover deferred resumes even when their owner was outside the selected handler
and was not unwound by the original search. Resume borrows an exact live
owner, or installs a fresh execution occurrence when it has ended. A borrowed
completion delimiter cannot pop the live original invocation. Control-owner
resolution does not rename retained boundary references or replay callback
entry. This is a realization candidate for the above control rule, with
arbitrary-source elaboration still open.

A thunk is a delayed `Run` with its lexical environment and required lineage.
Construction returns the thunk without running any body step, mutating the
source store, emitting a request, or generating a body event. Lexical typed
references are retained, not activated into grants. Lookup, storage, passing
and return of this first-class value do not by themselves execute it. `Force`
executes that delayed relation under the current configuration, using the
same state-threading bind. Each request exposed by force retains its own
origin and `K,D`; force may allocate a new dynamic event identity but cannot
relabel the source origin or discharge a still-live formula. Function/result
adaptation is also ordinary composition: a force occurs exactly where the
source consumer relation demands the value. The complete `CallView` includes
argument adaptation, body execution, result adaptation, and every force
before the enclosing handler dispatch.

An operation value uses the same invocation entry, with its declaration
determining the payload parameter role:

```text
ApplyValueν(Operation(op,decl),t,C) =
  Invokeν(entry_from_decl; native_body,t,C)
native_body(a) = Return(MakeRequestThunk(op,a))
```

Here `Invoke` is the common receipt/entry/body relation above, with one
invocation and its normal return delimiter. For a declared value payload
`a:A`, entry forces `t` and rebinds the result as `a:A` before the native body
constructs the latent request. For example, an operation `Unit → Unit`
receiving `Delay(Return Unit)` stores the resulting `Unit` as its payload,
not the argument carrier. A declared computation payload instead retains
its carrier according to its declaration; entry does not force all payloads
indiscriminately. `MakeRequestThunk` is an internal constructor, not a public
callable or another invocation, and emits no request. Declaration-role and
typed-correspondence elaboration remain premises.

Requests during entry retain the rebinding/native-body/return suffix under
the same bind and owner/raw-resumption rules. Construction preserves the
source origin, operation-instance endpoints, symbolic `K,D` and corresponding
payload/result incidences; it creates no operation arm or capture grant.
A source-demanded `Force` of the returned thunk yields `Request(q,C,k)`.
This keeps thunk construction distinct from request emission; equivalence
to the frozen placement of entry force remains unproved. The
source typing/evaluation rules must establish the exact force position in a
`CallView`. Generated requests get the generating transition's origin;
inherited requests preserve their origin through closure, thunk, adapter,
bind, and resumption transport. If a formula constrains any
output/residual/value view, the transition carries it and its `D` incidences
together, even when the request is not in immediate support.

## 4. Callback boundaries and candidate visibility

The user's typed-value transport decision is recorded in charter §13.
The common relational realization in
`2026-10-02-typed-boundary-realization-draft.md`, §6, refines the boundary
relevance used here: evidence follows corresponding typed value paths through
arguments, environments, store, results and adapters. A current receiver-local
explicit contract discharges transported callback protection for that event;
an inherited protection does not independently veto it. Outer receiver grants
do not authorize nested owners. Persistent source profile metadata is distinct
from incidence derived for an exact currently active handler. No additional
invalidating source boundary is defined by this ordinary package. Source
profile elaboration and re-entry ownership remain realization premises.

`Visibleν(q,h,C_h)` is checked at the actual configuration `C_h` where
ordered search tests handler activation `h`. It requires that `h` is active in
the current ordered activation sequence, that no applicable source boundary
on this event's derivation excludes `h`, and that `h` covers the exact
operation. A callback contract applies only when the event's observed typed
view is related to that boundary by corresponding typed paths and the
candidate owner receives the same view. This includes the original complete
call/adaptation/force view and later latent views reached through a matching
result path while the receiver remains active. An ordinary request from the
receiver's own body does not need callback incidence. Search examines
candidates in order; visibility is never computed once for a whole stack.
After closure escape, exited maker activations are absent and no historical
maker mask is consulted. `OpCompatν` is a separate typing condition on every
arm actually selected; it cannot change runtime selection or turn an
incompatible selected arm into forwarding.

The ordinary search path is the active source activation sequence itself.
Dispatch tests the innermost active handler first. Forwarding crosses that
handler by the shallow-handler rule and proceeds to the next active candidate;
selection exits the selected handler for its arm, while raw resumption resumes
outside that selected activation. These are transitions over existing call
and handler activations, not an additional boundary mask. For an event whose
derivation crosses the relevant callback argument boundary, `Capture`
constrains the receiver-local candidate through its explicit callback
contract; it is not retained after that receiver activation exits.

For a higher-order receiver activation `r` with callback argument boundary
`a`, distinguish its annotation forms. A concrete capture annotation names
the families exposed to a handler inside `r`; a wildcard surface annotation
describes a public row and does not itself grant capture; an omitted callback
annotation supplies no new capture contract; a concrete result annotation is
a static escape filter, not a capture grant. These distinctions follow the
frozen public reference and remain independent of the inferred residual row.

A callback-capture incidence is a join in the complete source relation, not a
consequence of row support alone. It applies only when the event's currently
executing typed view is connected to callback boundary `a` by the typed
correspondence relation and the source computation relation observes that
event at the corresponding effect port:

```text
Captureν(q,h) iff
  h is a handler activation installed by r, and
  Active(h,C) ∧ Active(r,C), and
  there are a boundary b and profile position p such that b.receiver = r,
  Inc_C(q,h,b,p), and Γ_b explicitly admits q.operation at p under ν
```

The event/boundary connection composes two distinct source relations: typed
`Flow` moves the boundary profile along corresponding value paths, while
`Observe(q,v,p)` relates the request to the effect port exposed by executing
view `v`; `Path` additionally requires that the receiver owns a typed receipt
for that same view. The observing view may be the callback's original complete
`CallView`, a nested view, or a later latent view reached from its returned
value along the signature's corresponding result path. In the latter case,
the original `CallView` observation has ended; the transported boundary
profile and the later view's own `Observe` witness establish the incidence
while receiver `r` remains active. An event may have observation witnesses
for several enclosing complete `CallView`s. The corrected context projection
in typed-boundary §4 records each executing view's marked computation port
before handler filtering; observation is not outward residual support.
Nested `CallView` entry therefore does not erase an
applicable enclosing receiver's incidence. This is the selected preservation
rule. The decorated context/routing theorem has clean package/repair review; source
elaboration and abstract identity correlation remain realization obligations.

The incidence is per request event and includes source-defined adaptation,
force, typed binding, storage, and result positions when the signature
correspondence relates those paths. Function-effect upper bounds constrain
which requests occur in callback behavior; neither those bounds, handler
ownership, family equality, nor support rows establish capture incidence. An
event generated by the receiver's own ordinary body uses ordinary ordered
visibility without a callback `Capture` premise. A later event from a returned
latent value uses the same relation only when its typed result path carries
the boundary profile and its later execution supplies the matching
observation; the outer callback effect position is not copied to that latent
position.

Visibility at the candidate handler is determined by the concrete typed
callback boundary visible there, not by hidden provenance of the computation
that produced the request. When the boundary exposes concrete effect `E`, an
`E` request exposed during the callback's complete `CallView` is eligible for
the receiver-local handler, including a request revealed by forcing a
caller-owned thunk, subject to ordinary ordered search and current
receiver-local eligibility as refined above. `Force` only exposes latent
computation; the callback contract supplies the authority. The request keeps its caller
origin, dynamic event identity, and symbolic `K,D`. Without a concrete
capture contract, no callback incidence follows. `[_]`, family equality,
surface rows, and handler ownership alone confer none. A direct callback
request and one revealed by `Force` have the same visibility under the same
concrete callback effect type. For example, under `(() -> [E] A)`,
`\() -> perform E` and `\() -> t` where `t : [E] A` have the same
callback-boundary visibility. The incidence ends with the receiver/handler
activation.

`Capture` is scoped to `(r,a,h,q,ν)`. The selected preservation rule
transports the boundary profile through each typed-value correspondence;
incidence for a request is then derived from that transported profile and
that request's own observation witness. This covers nested calls, adaptation,
`Force`, captured bindings, stores and corresponding returned latent paths
while the same receiver and handler activations remain active. It does not
grant eligibility to a new nested handler. When search leaves `r`, its handler
frames and incidence are no longer active; latent effect, origin, `K,D`, and
runtime lineage remain.

The selected candidate rule above treats direct callback requests and
caller-owned requests exposed by nested `Force` as instances of one callback
`CallView`. It does not make `Force` a source of authority. Their shared
visibility follows from the same concrete callback effect type; their origins
and `K,D` remain event-specific. A caller-owned request evaluated by the
receiver's own body is outside the callback relation and uses ordinary
visibility. Thus the typed boundary determines eligibility while provenance
remains an independent observation in the common relation.

At a handler outside an exited receiver, visibility is derived from the
ordinary current boundary path after the actual unwind. No premise asks that
the old receiver's callback contract be copied to the outer handler, and no
premise keeps that contract as a blocker. Other currently active source
boundaries still apply at their own candidate activations. This single
candidate-indexed relation gives the three cases:

- A direct effectful closure uses ordinary application and current-handler
  search; it has no callback `Capture` premise.
- An escaped callback closure keeps its latent request and runs under the
  later caller configuration. Its maker activation is absent, so only current
  caller boundaries and ordered search determine eligibility.
- A mixed-origin computation keeps each event's own origin and `K,D`.
  Callback-contract incidence for one event cannot authorize another event
  merely because the operation family is equal.

This is a common scope relation, not a callback-versus-ordinary selector. The
source-adequacy theorem must show that every source call/adaptation/force
transition produces exactly the `CallView` incidences of the selected
typed-boundary relation. The runtime lineage
mapping and candidate configuration must preserve every eligibility-relevant
coordinate, including active frames, request IDs, and live state. The
ordinary caller eligibility after escape follows from the active-sequence
search rule once the ordinary closure-application transition has returned the
body computation to that caller configuration; proving that transition and
its complete-interface transport belongs to milestone 2.

## 5. Shallow handler image

For `catch H` the source relation applies one image transformer to the complete
resumable computation, not a subtraction on its immediate row projection.
On `Return(v,C)`, the value arm runs after the selected handler activation is
left. On `Request(q,C,k)`, ordered search examines candidates in source order
at their actual post-unwind configurations. Pattern and guard evaluation keep
their state and effects in the same relation. A candidate can select only if
`Visibleν(q,h,C_h)` holds and its pattern/guard accepts.

If an arm at `h` selects, it runs outside `h` and receives the raw `k`. The
raw continuation is not automatically wrapped with the selected shallow
handler. If the arm resumes it, later requests enter their own current
search; the arm must explicitly rewrap the continuation to catch them again.
If no arm selects, search forwards the request after unwinding frames crossed
to the outer candidate and wraps the continuation only with the source
re-entry needed to resume the still-enclosing handler computation. This
preserves call/handler order without a special callback rule.

The handler output is the relational image of all such request, return, guard,
pattern, and resumption paths. Immediate support is projected only afterward.
Thus handling one request cannot erase a possible raw-suffix request, and a
typed-family formula remains if any continuation, residual, root, or latent
value still depends on it. Soundness requires the inferred handler result to
overapproximate this complete image. Principality is relative to the selected
finite interface language, not to exact continuation-use counts.

Charter §§14–15 record **outside** selection and primitive shallow handling.
The original request's applicability is a fact of its yielding body boundary;
the selection computation executes after the candidate exits. Matching,
its finish continuation and the selected arm run in the outer context by
ordinary bind. A new selector/arm request has its own current-context
dispatch. Exhaustion forwards the original request with only the ordinary
forwarding wrapper; the raw suffix passed to a selected arm does not regain
the selected handler. Typed-source-owner §6 supplies the reviewed equations
and pending-match preservation proof. Thus later completion of the original
match requires no live reference to the expired candidate.

### Primitive shallow image and explicit deep reapplication

The source has one primitive handler image, the shallow image above. Selection
includes ordered arm search, pattern/default/guard evaluation and completion;
all of that computation runs outside the candidate. The applicability premise
uses the original request's typed boundary evidence. Reading that premise
does not evaluate user code under the candidate or retain its live authority
for a selector's new request. Every store access during selection uses the
current outer state.

Write `S_H[c]` for the shallow image of computation `c`, and use brackets to
emphasize that `c` executes inside that image. Define a derived recursive
source expansion `D_H` by wrapping the continuations supplied by `H`:

```text
wrap_H(k) = λa. D_H[Resume(k,a)]
D_H[c]   = S_{H with each exposed raw continuation k bound as wrap_H(k)}[c]
```

This notation specifies an explicit source expansion, not a second primitive
handler mode. The transformation is capture-avoiding and applies wherever
that continuation binding is visible, including a continuation-binding
pattern or guard that uses it, the selected arm, and a closure retaining it.
Return/value arms have no newly supplied operation continuation to wrap.
An exhausted search retains ordinary shallow forwarding of the original raw
request/suffix; applying the transformed handler on that forwarded suffix is
the same derived `D_H`, not a second additional wrapper.

Reapplication encloses execution of `Resume(k,a)`. A call-by-value helper that
first evaluates `Resume(k,a)` and handles only its returned value is not this
expansion; a helper must receive a delayed computation and execute it inside
the reapplied shallow image. The source expansion's actual calls, signatures
and typed paths govern owners and capture contracts. The notation neither
copies an old capture grant to a fresh owner nor restores an expired handler.
If the expansion needs a typed callback contract, ordinary source typing must
derive it; the word "deep" supplies no authority or annotation.

**Expansion law.** Every finite execution/future-interaction prefix of this
derived form is an execution of its shallow source expansion, with the same
returns, requests, current store, activation ordering, typed boundary views
and joint `ν,K,D`. The proof relates the derived call to one unfolding of the
displayed recursive source definition. Continuation wrapping constructs a
latent closure; it does not execute the raw suffix. Invoking that closure
enters a fresh shallow handler occurrence around the raw resumed computation.
The ordinary shallow rules then perform selection/guards/arms outside that
occurrence. A further invocation uses another unfolding, with the same
captured typed environment and current state. Ordinary bind and context
preservation compose the steps, including multiple uses of the continuation.
Requests raised by a selector or arm before invoking the wrapped continuation
stay outside the candidate; no equation moves them under it. Forwarding uses
the transformed shallow descriptor once. Induction on finite source steps
and future invocations proves the claim; infinite runs retain all finite
prefixes. This proves a definitional source expansion, not a new type-safety
or principal-inference theorem for recursive definitions.

A finite handler body produces a finite recursive expansion with shared code;
each continuation binding has one wrapper body referencing that definition.
This is a code-template bound, not a bound on dynamic handler occurrences or
a finite inferred scheme. An implementation may recognize this expansion,
but must prove equivalence to the complete source relation, including new
handler/owner identity, outside selector effects, raw suffix order, all future
uses and symbolic typed-family transport. No optimization is authorized here.

## 6. Ordinary-flow / escaped-callback theorem

**Ordinary-flow consequence (caller handling after closure escape).**
Suppose:

1. receiver activation `r` returns closure `d` normally, so handler
   activations owned by `r` leave the active configuration;
2. the returned value relation retains `d`'s latent request interface, each
   request origin, symbolic `K,D`, and required runtime lineage;
3. a later application of `d` occurs in current configuration `Cnow`, and
   ordinary `ApplyValue`, source-demanded `Force`, and stateful bind expose
   event `q` without changing its origin or dropping its live `K,D`;
4. in the actual post-application search configuration `C_h`, ordinary ordered
   search reaches active caller handler `h` before any earlier handler
   selects; every applicable current source boundary admits this event for
   `h`, `h` covers the exact operation, and the selected arm satisfies
   `OpCompatν`.

Then `Visibleν(q,h,C_h)` holds. If its pattern/guard selects that compatible
arm, `h` handles `q` at `C_h`. No `Capture` premise
from `r` appears: `r` and its handler activations are absent at the fresh
call. Other current callback/source boundaries still constrain their own
events. A direct effectful closure follows the same dispatch. In a
mixed-origin execution the argument applies independently to every event.
After a shallow selection, a resumed raw suffix is tested in the configuration
outside the selected handler and needs its own visibility and compatibility
derivations.

The ordinary caller case is closed relative to the current-configuration
search rule: after maker return, a fresh caller handler is tested by the same
ordinary active-handler/boundary relation as for any direct effectful closure;
there is no maker `Capture` premise or persistent maker mask. This is a
source-rule consequence, not an inference from family equality. Source-to-
complete-interface adequacy for all supported expressions remains the next
theorem package.

## 7. Proof order and non-goals

This package records the coherent candidate ordinary source rules for the
supported call/closure/force/request/shallow-handler sublanguage. The selected
callback-incidence preservation rule follows the user's decision through the
complete callback call view without a historical maker mask. The user's
2026-10-02 decision fixes visibility by the concrete typed callback boundary:
direct requests and requests exposed by caller-owned `Force` have equal
eligibility under that type, while origin and `K,D` remain distinct. The
source ownership map per scheme lookup is specified in the adequacy candidate
and still needs theorem-level validation.
Prove source-to-complete-interface adequacy for the complete machine,
including all force/adaptation positions, ordered visibility, callback origin,
shallow raw resumptions, and transport of `ν,K,D`. Then derive a finite
symbolic presentation and prove its soundness/principality. Only after that
prove generalization, fresh instantiation, and SCC intrusion preserve the
presentation. Perform the next implementation-feasibility gate after those
semantic obligations identify the required compiler surfaces.

Method selection, roles, and implementation resolution remain a later
mandatory gate. Exact trace support remains the soundness reference, not a
requirement on the finite inference abstraction. Oracle weight routing is
characterization evidence only. Any Oracle difference accepted for
soundness/principality must have a concrete conflict witness, the behavior
dropped, the successor rule, and final-acceptance impact recorded before it
is treated as an accepted compatibility difference.

No implementation is authorized by this draft. The concrete callback-boundary
rule is selected by the user's 2026-10-02 decision and received focused
compiler-referee delta review with no major finding. The exact-interface
theorem package also received compiler-referee review with no major finding;
the candidate semantics now advances to finite presentation and principality.
