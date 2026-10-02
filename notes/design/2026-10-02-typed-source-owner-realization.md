# Typed source transport and resumption ownership

Date: 2026-10-02
Status: Draft; owner/control and typed-view context extension reviewed; outside selector extent selected by user; full source realization open
Scope: ordinary decorated source control, typed value transport and live owner realization
Approved-by: user for charter §§13–14 transport/lifetime and outside selector extent; concrete realization unapproved
Drafted-by: primary with bounded resumption-owner architect input
Reviewed-by: compiler_referee and spec_auditor initial package reviews; fresh compiler_referee delta review found no major issue, two minor findings addressed by primary
View-extension-review: compiler_referee and spec_auditor projection package; extended constructor-scope clarification closed by independent compiler_referee delta, 2026-10-02
Supersedes: none

## 1. Claim and exact input

This package makes the owner mapping left open in typed-boundary realization
§6 explicit. It also states one preservation theorem for that mapping and
the common typed transport through the ordinary source machine. It introduces
no new callback-specific source construct. Execution owners and continuation
delimiters are control bookkeeping; boundary profiles remain source contracts.

Fix one finite monomorphic decorated source descriptor graph `Ω` and one
assignment `ν`. Its code covers binding, closures/thunks, cells, call/force,
requests, source structural adapters, stateful guards, shallow handlers and
raw resumptions. Every typed value-flow edge has its source/target signature
ports. Explicit callback contract occurrences are distinguished from public
rows, omission and static result filters. Finite profiles and correspondences
are those supplied to the reviewed typed-boundary transport theorem.

This input is stronger than parsed Yulang syntax. In particular, syntax-v0's
type-expression and bracket-row references define grammar, not annotation
meaning or typing. This theorem does not derive all annotation roles or
unknown constructor shapes from unelaborated syntax. The fixed-shape adapter
kernel remains a candidate with its own declared structural equivalence;
no general conversion is silently selected here.

## 2. Source owner spans

Separate a logical invocation descriptor `i` from each dynamic execution
occurrence `u`. Each `u` is a fresh identity with descriptor `i`. Handler `h`
has an exact current owner `u`. A normal source call allocates a fresh `u`,
binds its argument and captured views, and enters its body. Its ordinary
return delimiter removes exactly that occurrence. Ending an occurrence is
irreversible for its identity; a new execution may have the same descriptor
but never the same expired identity.

Saved source control is a finite evaluation context for each finite capture:

```text
K ::= Hole
    | Bind(K,F)
    | Owner(i,u,K)
    | ForwardHandler(H,ownerSlot,K)
```

`F` is a source suffix label together with its typed lexical environment;
it is defunctionalized ordinary source code, not an opaque host function.
`H` is the source handler descriptor and its saved environment. `Owner`
records the invocation containing its child context, including when its
owner was outside the selected handler and was not unwound by search.
Recording only crossed call frames would lose that owner's deferred code.
These records contain code, views and cell references, not a mutable-store
snapshot or a historical caller stack.

Typed-boundary §4's corrected observation candidate extends this grammar
with `View(v,p,K)` for crossed executing typed-view delimiters. Its separate
context-projection theorem treats these as computation scopes, distinct from
executable `Owner` attribution. A borrowed owner can execute inside a new
caller's view; owner resolution must preserve that ambient context. Crossed
views re-enter with fresh execution occurrences and original typed packets;
they do not rebind boundary receivers. The extension and its constructor-scope
clarification have clean independent review within the decorated kernel.

Plugging a response into `Hole` supplies that response and the current live
configuration. `Bind(K,F)` executes its child and then `F` by the ordinary
state-threaded bind: a return passes its value and resulting configuration to
`F`; a request retains `F` after every resumption of its child. Thus a child's
completion continues its captured parent suffix before the parent completes.
A raw continuation has a separate root capture delimiter. Only that root
installs `ResumeReturn` to the current resumer; no internal `Owner` or `Bind`
delimiter installs it.

At each invocation of a raw continuation, create a fresh *control* environment
`ρ` and local pending frames for this context. On entry to `Owner(i,u,K)`,
resolve its saved occurrence against the current active configuration:

```text
enter(i,u,C) =
  (u, borrowed, C)                       if Active(u,C)
  (u′, owned, push Call(i,u′) onto C)      otherwise, u′ fresh

leave(borrowed,u,C) = C
leave(owned,u′,C)   = remove exactly the entered u′
```

The entered owner binds its executable owner slot for the child, saving the
previous lexical binding and its completion action in a pending frame.
Source context nesting determines entry order. On a child return, that frame
performs `leave`, restores the previous binding, and passes the value and
current store to its parent context. A borrowed completion never removes the
still-running original call. An owned completion removes only its entered
occurrence. Neither returns directly to the resumer. Repeated references
within the owner use its one resolved occurrence; nested owners shadow it.
Handlers and new receipts use that current owner. A genuine new call made by
`F` allocates its ordinary fresh occurrence with its own nested return frame.

Entry to `ForwardHandler(H,ownerSlot,K)` installs the source-prescribed fresh
handler under the currently resolved owner slot and executes its child through
the complete source shallow-handler image. On a normal body return it exits
that exact handler and runs the ordinary value-arm computation; only that
computation's result continues the parent context. Its requests retain that
parent continuation by ordinary bind. The value arm is not skipped merely
because this is a re-entry wrapper.
Capture composes contexts by replacing `Hole` with the captured inner context:
ordinary bind contributes `Bind`, invocation control contributes `Owner`,
and shallow forwarding contributes only its source-prescribed
`ForwardHandler`. The selected shallow handler's computation delimiter stops
capture and contributes no handler wrapper. It bounds the saved context;
source control beyond it is the current resumer's continuation. A containing
invocation may supply the owner of code inside that bound, but this does not
append that invocation's code outside the selected computation.

For example, an outer handler selects `A` emitted by `g` during `f`'s call
of `g`, and `f`'s suffix after `g` emits `B`. With `Kg` the remaining code
of `g` and `Ff` the captured suffix of `f`, the saved control is

```text
Owner(f,uf, Bind(Owner(g,ug,Kg),Ff))
```

Raw resume enters `f`, then `g`; runs `Kg`; closes `g`; runs `Ff` and exposes
`B`; after `B` is answered and `Ff` completes, closes `f`; then reaches the
root `ResumeReturn`. Every step uses the current store. Returning directly
from `g`'s delimiter to the resumer would incorrectly skip `Ff` and `B`.

Suspension reconstructs the remaining context from the executing suffix and
its local pending frames, retaining each unfinished bind, owner completion,
and source-prescribed forwarding wrapper up to the selected capture root.
It saves the *currently resolved* occurrence in each executable owner slot,
without substituting it into retained boundary evidence. Search unwind may
end an owned occurrence; a later entry resolves that saved identity again,
and its completion uses the newly entered mode/occurrence, never a stale pop.
Completed children are not replayed: their resulting value and the remaining
source suffix determine the new hole. Each multi-shot invocation has its own
pending frames and `ρ`. Reuse is allowed without a use-count condition.

## 3. What owner resolution does not rename

`ρ` is a control environment, not a type substitution or evidence transport
map. Resolution changes only executable owner slots, matching control return
delimiters and newly allocated handler owners. In particular it does not
rewrite:

```text
b.receiver, old Receive owner, χ profile roots, stored typed value views,
request origin/event, symbolic endpoints, K or D.
```

Loading a saved typed binding into the resumed span creates an ordinary
`Receive(current owner,slot,view,Id)` edge using the existing receipt rule.
It creates no boundary and no concrete contract. Old receipts stay in the
evidence graph; activity decides whether they can participate in current
incidence. If the original receiver is dead, a new execution owner cannot
make its boundary live by sharing code or type with it.

Only an actually executed source boundary-entry operation introduces a fresh
boundary instance from its explicit contract descriptor. Entering a saved
owner span resumes after the earlier entry; it does not replay that entry,
rebind its callback contract to `u′`, or relabel old values. If new source
calls/typed boundary entries occur later in the suffix, they introduce their
own fresh instances by the ordinary rule.

For handler control, selected shallow `h0` has no re-entry wrapper. A
source-prescribed forwarding wrapper may instantiate a fresh handler `h′`
at the correct source nesting position under the resolved owner. Its old
descriptor/environment is reusable; its expired activation identity and
incidence are not. It checks current `Inc_C(q,h′,b,p)` from typed-boundary
§6. Handler re-entry is not itself callback boundary entry. Existing live
handlers are exactly those reached by the current active roots.

## 4. Uniform transport and ownership invariant

Relate a decorated source state to its explicit owner/view graph by joint
decoding, with fresh identities related bijectively. Keep these clauses:

1. Every executing source span has its current active owner and matching
   local completion frame; handlers name the corresponding current owner.
   Saved control in the original owner fragment is composed from the four
   context constructors in §2; the typed-view extension additionally has
   `View(v,p,K)` and preserves typed-boundary §4's executing-context projection;
   internal completion continues its parent, and only the capture root
   returns to the current resumer.
2. Every typed binding, environment entry and stored value retains its view.
   Each output view contains exactly the indexed relational image of its
   input evidence under its declared typed correspondences.
3. Evidence retains original boundary/receipt identity. Candidate incidence
   is derived using the exact current handler, owner and original receiver;
   saved reachability alone proves none of them active.
4. Requests retain source origin, event identity and all dependent `K,D`
   under the same `ν`. Owner resolution does not act on these coordinates.
5. Saved suffixes retain code/views and cell references, while reads/writes,
   guards and resumes use the current live store. Raw selected continuations
   contain no automatic wrapper for the selected shallow handler.

**Preservation theorem candidate.** Starting with a related initial state, every finite
ordinary decorated source execution has a matching owner/view graph execution
preserving these clauses. Each finite sequence of later calls, forces and
well-formed raw resumptions also preserves them. In the typed-view extension,
the theorem includes `View` entry, completion, capture and re-entry, using the
typed-boundary §4 projection invariant together with these owner clauses.
This is an operational
realization theorem, not a proof of full source type safety or principal
inference.

**Proof construction.** Induct on the primitive transition derivation, including transitions
made by a saved suffix rather than assuming a suffix is an opaque host action.

- Initialization allocates the source's initial live owner occurrences and
  introduces only its actual boundary entries. Initial views, predicates and
  dependencies are copied with one consistent fresh-identity map.
- Binding, lexical capture, store read/write and return use the same
  multi-input relational image. Its identity, composition and union laws
  establish clause 2 regardless of which of these storage paths realizes a
  composite typed edge. Actual result evidence and matching signature result
  evidence remain separate inputs; raw-pointer equality adds no input.
- Call introduces a fresh occurrence with its matching normal delimiter.
  Existing views supply receipts to that owner; only its actual callback
  boundary entries introduce contracts. Closure construction captures views,
  not active owner roots. `Force` and descriptor adaptation compose the same
  typed edges and source transitions, so they create no extra authority.
- Request observation composes its actual typed view with the complete
  current CallView. It copies the event's joint symbolic data. Ordered search
  evaluates the graph relation for each exact candidate configuration;
  identical decoded roots and witnesses give the same visibility and same
  guard execution. `OpCompat` remains a check on the selected arm.
- Normal return, search unwind and shallow selection remove exact active
  occurrences. The live-filter law removes their incidence without modifying
  views or predicates. Selection omits its handler wrapper; forwarding adds
  only source-prescribed wrappers in source order.
- Resume enters owner spans by the two disjoint activity cases. A borrowed
  span leaves the current occurrence active; an owned span allocates a fresh
  occurrence. Neither branch rewrites historical evidence. Fresh receipts
  follow the existing receipt rule. Structural induction on saved `K`
  establishes clause 1: `Hole` supplies the response; `Bind` retains and runs
  its source suffix after child completion; `Owner` enters before its child
  and closes only its own entered occurrence before continuing its parent;
  `ForwardHandler` installs/exits its exact fresh handler under the resolved
  owner. In the typed-view extension, `View(v,p,K)` enters its executing
  observer delimiter before its child and completes through its parent;
  capture saves crossed views and re-entry restores their scopes with fresh
  occurrences and original typed packets. Typed-boundary §4's projection
  invariant preserves the ambient view even for a borrowed owner, without
  rebinding receiver authority. Only the separate capture root installs
  `ResumeReturn`. Context
  substitution preserves these nesting/completion clauses, including requests
  from a bind suffix. Capture stops at selection and omits that handler's
  wrapper. Suspension rebuilds unfinished frames with current resolved slots;
  re-entry repeats the activity cases rather than replaying stale completion
  actions. Current-state threading establishes clause 5; fresh handler
  wrappers recompute eligibility without renaming retained evidence.

Ordinary sequencing and adapter/force sequencing contribute `Bind`, calls
contribute `Owner`, and shallow forwarding contributes `ForwardHandler`;
selection supplies the capture bound. These four constructors exhaust the
original owner fragment. The typed-view extension additionally contributes
`View`; its entry, completion, capture and re-entry cases are covered by the
projection invariant above. Together these cases exhaust the saved control
of the declared decorated descriptor operations, while the primitive cases
above cover their value/store/request steps. Induction
also covers arbitrary finite multi-shot interaction histories: each resumed
execution is another sequence of the same cases in the current state. No
affine restriction, persistent maker mask, or origin-sensitive exception is
used. Infinite behavior is covered at every finite prefix.

**Expiry consequence.** Once `u` or `h` ends, none of the transitions makes
that identity active again. Hence all incidence requiring it remains false.
Fresh control occurrences can execute saved code but cannot resurrect the
old capture/protection. Live outer receivers retain their exact identities,
so their applicable grants remain available under the reviewed relation.

## 5. Effective realization and remaining boundary

The initial semantic review found that an intermediate owner completion was
incorrectly described as returning directly to the resumer. Section 2 now
gives inductive control contexts, parent completion and a separate root
return. Fresh semantic delta review found no blocking or major issue in that
repair or the conditional selector account. Two minor issues were addressed
by clarifying the typed discriminator and recording the existing coupled-core
outside-context candidate language. The conformance review found no authority
violation. The user subsequently selected its outside extent in charter §14;
this closes that source choice without certifying the remaining full-source
realization premises.

The selected selector extent is explicit in §6. Under its outside-image
equation, the guard/match continuation runs as `Bind` outside H, so it
contains no live candidate-handler reference. The fresh semantic delta review
found no major defect in this conditional account or the parent-completion
repair. Charter §14 now supplies its outside premise. The typed-view
projection/control theorem is also reviewed within its stated decorated
inputs; arbitrary-source elaboration remains a separate proof obligation.
The discarded inside alternative needs no further proof.

The four saved-context constructors of the original owner fragment and the
additional `View` constructor of the typed-view extension, source suffix
labels with typed environments, owned/borrowed pending frames, observer
frames, control environment links and the separate root `ResumeReturn` have
bounded record fields. View records retain finite static descriptor references
and dynamic links; the typed-boundary §4 projection governs their executing
and saved states. Entry traverses
context nesting one record at a time; completion follows its local pending
parent frame. Suspension rebuilds the finite remaining context from those
frames. `enter` walks the current active roots to test the exact saved
identity; allocation uses a fresh concrete address. `leave` uses the matching
entered occurrence. A finite execution prefix has finite control and
active/evidence graphs, so each administrative lookup terminates. It does
not unfold recursive code or signatures.

Together with supplied finite profiles/maps and the reviewed adapter kernel,
this constructs the local owner/bind/transport records and instructions for
source-realization §4. Completing the pending-search control obligation and
independent repair review is required before claiming realization of the
whole ordinary kernel. The generic finite-address simulation can represent
these record tags. Ambiguous abstract identity/activity tests
retain both outcomes; no collision proves an expired occurrence live.
This does not establish exact acceptance of that abstraction.

The precise remaining inputs are finite source annotation-role/profile
elaboration and general adaptation, including unknown shapes, plus uniform
open-client interaction and the source typing/acceptance bridge. A finite
presentation for each linked decorated program is still not a reusable
principal scheme for every future client. Lifecycle and compiler
implementation remain downstream. This package does not claim that the
chosen abstract judgment already accepts every intended well-typed source.

## 6. Selector extent: localized source decision

The remaining guard obligation cannot be settled by renaming a handler ID.
The extent in which the handler's own pattern/default/guard computation runs
must be specified. Syntax-v0 `expressions/case-catch.md` explicitly excludes
guard/handler semantics from its authority. The coupled core already records
in prose that guard effects run in the outer active context
(§`Step_H`, lines 849–859), but that core remains a Draft and not an
authoritative successor decision. This package makes its outside interpretation
explicit and derives its continuation consequence.

### Source-level discriminator

Use operations `E : Unit -> Int` and `P : Unit -> Bool`, and common handler
result type `Int`. Every operation arm and value arm below returns `Int`;
the E and P guard arms deliberately do not resume their continuations. This
gives compatible answer types under the ordinary effect-operation typing
direction. It is still semantic pseudocode, not an executed or accepted
Yulang fixture:

```text
outer H0:
    P(_,k) -> k(true)
    E(_,k) -> k(7)
    v      -> v
inner H1:
    E(_,k) if perform P() -> 0
    E(_,k)               -> 2
    P(_,k)               -> 1       // does not resume k
    v                     -> v
body of H1: perform E()
```

If H1 surrounds its own guard computation, the guard's `P` can select H1's
`P` arm and return `1`, aborting the suspended E selection. If matching runs
outside H1, `P` goes to H0; resuming it with `true` completes the pending
guard and chooses the original E arm, yielding `0`. There are no callback
contracts or type-family tricks in this distinction. Both computations use
the displayed ordinary payload/result types and identity value arms. The
inside policy wraps the whole selector plus its `Finish_H` in H1's handler
answer delimiter; handling only the guard expression with an `Int`-answer
handler would be ill-typed because that expression supplies `Bool`. Thus this
is a source execution choice, not interchangeable owner bookkeeping or a new
callback exception.

The user selected the outside interpretation on 2026-10-02 (charter §14).
The comparison records the observable choice rather than an open question. “Inside” and
“outside” describe two uniform policies for the entire selector/finish
computation; they are not an exhaustive list of every possible mixed policy.
No mixed policy has been selected. This choice closes the extent premise of
the reviewed proof; it does not approve implementation or the acceptance bridge.

### Characterization evidence

Frozen `a58eefc3:crates/mono-runtime/src/runtime/eval.rs` has these control
facts: `eval_catch` evaluates its body and then calls `handle_catch_result`;
`handle_catch_request_arm` uses `continue_bind`/`continue_with` for patterns,
continuation binding and guards. A guard-emitted request is returned by that
ordinary continuation composition, without applying the same catch image
to it. Only exhausted arm search wraps the *original* request's raw
continuation with `handle_catch_result`. The value-arm path likewise evaluates
matching outside the catch body image. These are immutable-source facts, not
test observations or successor semantic authority. The evidence-vm
`eval_catch` also removes its active catch entry before dispatching its body
result; this is corroboration, not a proof of full backend equivalence.

### Selected outside-image equation

Selector computations run outside the candidate by charter §14. Let `H[c]` mean
apply the shallow handler image to body computation `c`, with its current
fresh activation while the body executes. Applicability of the original
request is defined by its actual yielding body boundary. Selection itself
executes after leaving the candidate, in the outer context (charter §15):

```text
H[Return(v)]       = MatchValue_H(v)              // outside H

H[Request(q,k)]    = MatchRequest_H(q,k) >>= Finish_H(q,k)
                    if q is eligible at H's current boundary

H[Request(q,k)]    = Forward(q, λa,Cnow. H[k(a,Cnow)])
                    otherwise

Finish_H(q,k)(Accepted(arm,bindings), C) = Run(arm.body,bindings,C)
Finish_H(q,k)(NoArm, C)                = Forward(q, λa,Cnow. H[k(a,Cnow)])
```

All equations thread the full current state and shared `ν`; the shortened
notation does not discard them. `MatchRequest_H` is the existing ordered
`BindPat`/continuation-binding/guard relation, ending in `Accepted` or
`NoArm`, not a new effect selector. Its code is ordinary source evaluation.
The arm receives the raw `k`, and static `OpCompat` constrains an actually
accepted arm without redirecting runtime search. A guard may itself invoke
that raw continuation; ordinary bind covers that computation too. Each
application of the displayed forwarding `H[...]` enters a fresh handler
occurrence, never the old one.

If matching emits `Request(qg,kg)`, the bind equation yields

```text
Request(qg, λa,Cnow. kg(a,Cnow) >>= Finish_H(q,k)).
```

There is no `H[...]` around this new request or its match continuation.
Consequently pending matching needs its source arm cursor, typed bindings,
original `(q,k)` and handler descriptor; it does not need an active reference
to the expired candidate handler. Suspending and resuming this computation
uses the same `Bind`/owner-span rules as any other source computation.

This completion concerns only the *original* event already tested at the
handler boundary. It grants no visibility for `qg`, a raw-suffix request, or
any later event. The historical eligibility test may remain in the proof
trace, but it is not a live `Inc_C` witness or transferable capture authority.
Once H exits, its live incidence remains false. This distinction is a
consequence of composing a handler image with ordinary matching; it is not a
new source ticket, obligation kind or stored grant.

The applicability premise is a judgment about the yielded request boundary,
not a selector computation running under the candidate. Thus the equations
implement outside **selection**, not merely outside arm execution. Deep
behavior is the explicit shallow reapplication defined in ordinary-computation
§5; it adds no special `Owner` or `ForwardHandler` constructor and supplies no
primitive deep-mode flag.

### Control preservation for the selected extent

For the outside interpretation, a pending match continuation is ordinary
source code plus its environment and cursor, so it is an `F` in §2's
`Bind(K,F)`. Structural induction on the ordered match relation proves:

1. mismatch/false guard advances the saved cursor using the current store;
2. a request retains exactly the remaining match and `Finish_H` composition;
3. a resumed accepted match runs its body in the resumed outer configuration;
4. exhaustion forwards the original `(q,k)` and current state, with H only
   around a future execution of that original suffix;
5. none of these cases reactivates an expired handler identity or rewrites
   a retained boundary receiver, event identity, or symbolic `K,D`.

The request case follows directly from the displayed bind equation and the
other cases from ordinary return sequencing. Induction over any finite
multi-shot interaction history repeats those same cases; it does not count
continuation uses or require a linear type. Pending-search handler rebinding
is unnecessary in this interpretation. The initially suspected stale-ID
case assumed that matching still ran under H; it is not a counterexample to
the outside-image equation.

The conditional lemma has a clean scoped semantic delta review: no blocking
or major finding; two minor findings were addressed here. The typed
discriminator now gives E an Int resumption and explicit identity value arms,
and specifies the answer delimiter needed by the inside policy. The existing
coupled-core outside wording is acknowledged as candidate evidence, not
treated as authority. No evidence settles mixed policies.

The selected outside interpretation refines the older informal
`Select(h,arm)` wording: eligibility is checked at H's body boundary,
while completion of that event's ordered match may occur later outside H.
Full source safety,
the finite principal presentation and acceptance equivalence are still not
proved by this control lemma. The inside interpretation would instead need
its own nested dispatch and handler-control preservation theorem; the two
cannot be equated by changing an ID map.
