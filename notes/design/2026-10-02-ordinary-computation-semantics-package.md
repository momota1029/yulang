# Ordinary source computation semantics: milestone package

Date: 2026-10-02
Status: Draft; receiver/Force scope unresolved; not implementation authority
Scope: calls, closures, thunk force, operation requests, callback boundaries,
and shallow handlers for the ordinary effect sublanguage
Supersedes: none
Inputs: user-selected soundness/principality priority, unified-relation
requirement, nested-capture preservation, ordinary escaped-callback handling,
and symbolic typed-family transport

## 1. Milestone claim

This package gathers the existing local evidence into one candidate source
machine. Its central choice is that a handler tests an event at the actual
configuration reached by ordered search. Ordinary visibility follows the
current active source configuration: a handler can handle an exact covered
operation when ordered search reaches it, subject to source-defined active
boundaries. No boundary belonging to an exited maker activation is carried
forward as a mask. Callback capture is the narrower contract relation used
when the candidate handler belongs to the active callback receiver; it is not
a property of an operation family or a value's historical maker.

Under this choice, normal return ends the receiver and its handler
activations. A returned closure keeps its latent computation, event origins,
symbolic typed-family predicates, and required runtime lineage. Its later
application runs under the caller's current configuration. A fresh caller
handler may handle a request when ordinary search and the current boundary
relation admit it. No maker boundary remains as a persistent mask.

The ordinary-flow / escaped-callback consequence follows from the current
configuration rule below: normal return removes the maker's activations, and
later search uses only the caller's active ordered handlers and their
source-defined boundaries. Review exposed one remaining scope choice for a
caller-owned thunk forced during a callback, which affects receiver-local
capture but not escaped-callback caller handling. This package records the
common machine shape and that exact fork; it must not be treated as frozen
semantics. Source/interface adequacy, finite principality, and intrusion
preservation remain later milestones.

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

Call-by-value application evaluates the callee, then the argument, then
applies the resulting values, threading one configuration through all three
stages:

```text
Runν(e₁ e₂,C) =
  Runν(e₁,C) >>= λ(f,C₁).
  Runν(e₂,C₁) >>= λ(x,C₂).
  ApplyValueν(f,x,C₂)
```

Applying a closure evaluates its body in the closure's lexical environment,
but starts from the current dynamic caller configuration. Required value
lineage is re-entered by this ordinary application transition. The closure
does not restore handler or receiver activations that have returned:

```text
ApplyValueν(Closure(body,ηcl,L),x,Cnow)
  = Runν(body,ηcl[x],Cbody)
```

`Cbody` is the output of the common closure-application transition from
`(Cnow,L)`. This notation adds no source construct or separate store; the
transition's exact lineage and boundary action is part of the machine whose
adequacy is tested in milestone 2.

A thunk is a delayed `Run` with its lexical environment and required lineage.
Construction returns the thunk without exposing its body requests. `Force`
executes that delayed relation under the current configuration, using the
same state-threading bind. Each request exposed by force retains its own
origin and `K,D`; force may allocate a new dynamic event identity but cannot
relabel the source origin or discharge a still-live formula. Function/result
adaptation is also ordinary composition: a force occurs exactly where the
source consumer relation demands the value. The complete `CallView` includes
argument adaptation, body execution, result adaptation, and every force
before the enclosing handler dispatch.

An operation value applied to its arguments constructs a thunk for one typed
request; it does not expose that request yet. A source-demanded `Force` of
that thunk yields `Request(q,C,k)`. This preserves the frozen call/force
boundary and keeps thunk construction distinct from request emission. The
source typing/evaluation rules must establish the exact force position in a
`CallView`. Generated requests get the generating transition's origin;
inherited requests preserve their origin through closure, thunk, adapter,
bind, and resumption transport. If a formula constrains any
output/residual/value view, the transition carries it and its `D` incidences
together, even when the request is not in immediate support.

## 4. Callback boundaries and candidate visibility

`Visibleν(q,h,C_h)` is checked at the actual configuration `C_h` where
ordered search tests handler activation `h`. It requires that `h` is active in
the current ordered activation sequence, that no intervening source boundary
has removed it from this request's search, and that `h` covers the exact
operation. Search examines candidates in order; visibility is never computed
once for a whole stack. On ordinary computation after closure escape, the
current caller configuration is the boundary path: exited maker activations
are absent, and no historical maker mask is consulted. For a handler installed
by an active callback receiver, its additional callback-contract eligibility
is the `Capture` relation below. `OpCompatν` is a separate typing condition on
every arm actually selected; it cannot change runtime selection or turn an
incompatible selected arm into forwarding.

The ordinary search path is the active source activation sequence itself.
Dispatch tests the innermost active handler first. Forwarding crosses that
handler by the shallow-handler rule and proceeds to the next active candidate;
selection exits the selected handler for its arm, while raw resumption resumes
outside that selected activation. These are transitions over existing call
and handler activations, not an additional boundary mask. Callback `Capture`
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
consequence of row support alone:

```text
Captureν(q,h) iff
  h is a handler activation installed by r, and
  the source relation connects request event q to callback argument boundary a
  in r's complete CallView, and
  the explicit capture annotation at (r,a) admits q.operation under ν
```

The incidence is per request event and includes source-defined adaptation and
force positions. Function-effect upper bounds constrain which requests occur
in the callback behavior; they do not by themselves establish capture
incidence. In particular, ordinary composition and origin preservation do
not decide whether a caller-owned thunk forced during the callback joins
`(r,a,h)`. The two candidate source contracts are:

| Candidate | Incidence rule for caller-owned thunk `t` forced during callback `a` | Handler image |
|---|---|---|
| Complete callback execution | If the request occurs in the complete `CallView` and the explicit capture annotation admits its exact operation, derive `Capture(q,h)` while `r,h` are active; keep the caller origin and `K,D` | The receiver-local handler may consume it; an outer handler sees only the residual behavior |
| Supplied-computation ownership | Preserve the caller origin but do not derive callback capture from `a` for `t` without another source connection | The request remains available to the outer handler; the receiver-local handler cannot consume it on the callback contract alone |

Both candidates distinguish a concrete capture annotation from wildcard
surface support, preserve per-event origins and `K,D`, and agree that no
receiver grant/mask survives normal return. The available source reference and
the user-selected escape rule do not choose between them. This is a genuine
source-scope decision; the first candidate must not be described as a theorem
of the Function upper bound.

`Capture` is scoped to `(r,a,h,q,ν)`. It can persist through nested calls and
adaptation while the same receiver and handler activations remain active and
the same event relation is transported. It does not create visibility for a
new handler installed by a nested receiver. When search leaves `r`, its
handler frames and this incidence are no longer active. The request's latent
effect, origin, `K,D`, and runtime lineage remain in the returned value or
continuation.

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
transition produces exactly these `CallView` incidences. The runtime lineage
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
4. ordinary search in `Cnow` reaches active caller handler `h` as a candidate
   before any earlier handler selects, `h` covers the exact operation, and the
   selected arm satisfies `OpCompatν`.

Then `Visibleν(q,h,C_h)` holds by the ordinary active-sequence search rule, so
`h` may handle `q`. No `Capture` premise from `r` appears: `r` and its handler
activations are absent at the fresh call. A direct effectful closure follows the same
dispatch. In a mixed-origin execution the argument applies independently to
every event.
After a shallow selection, a resumed raw suffix is tested in the configuration
outside the selected handler and needs its own visibility and compatibility
derivations.

The ordinary caller case is closed relative to the current-configuration
search rule: after maker return, a fresh caller handler is tested by the same
ordinary active-handler/boundary relation as for any direct effectful closure;
there is no maker `Capture` premise or persistent maker mask. This is a
source-rule consequence, not an inference from family equality. The
caller-owned-`Force` incidence above remains a separate receiver-local scope
decision and does not reopen this escape consequence. Source-to-complete-
interface adequacy for all supported expressions remains the next theorem
package.

## 7. Proof order and non-goals

This package is a milestone-1 candidate, not a closed milestone. The ordinary
caller-after-escape consequence is settled relative to the active-sequence
rule; resolve the receiver-local callback/`Force` scope and delta-review that
clause, then freeze milestone 1. Next prove source-to-complete-interface
adequacy for the complete machine, including all force/adaptation positions,
ordered visibility, callback origin, shallow raw resumptions, and transport
of `ν,K,D`. Then derive a finite symbolic presentation and prove its
soundness/principality. Only after that prove generalization, fresh
instantiation, and SCC intrusion preserve the presentation. Perform the next
implementation-feasibility gate after those semantic obligations identify
the required compiler surfaces.

Method selection, roles, and implementation resolution remain a later
mandatory gate. Exact trace support remains the soundness reference, not a
requirement on the finite inference abstraction. Oracle weight routing is
characterization evidence only. Any Oracle difference accepted for
soundness/principality must have a concrete conflict witness, the behavior
dropped, the successor rule, and final-acceptance impact recorded before it
is treated as an accepted compatibility difference.

No implementation is authorized by this draft. One bundled theorem-package
review has been completed and its findings incorporated; the remaining
receiver-local `Force` scope choice requires explicit user approval, followed
by a delta review of that clause, before this document can become
authoritative.
