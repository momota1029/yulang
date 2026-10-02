# Typed source transport and resumption ownership

Date: 2026-10-02
Status: Draft; initial package reviewed; completion-routing repair awaits independent closure; pending-search control obligation open
Scope: ordinary decorated source control, typed value transport and live owner realization
Approved-by: user for charter §13 transport/lifetime principles; concrete realization unapproved
Drafted-by: primary with bounded resumption-owner architect input
Reviewed-by: compiler_referee and spec_auditor initial package reviews; major completion-routing finding repaired but not independently closed
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
handler under the currently resolved owner slot and executes its child. Its
normal completion exits that exact handler and continues the parent context.
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
   Saved control is composed from the four context constructors in §2;
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
well-formed raw resumptions also preserves them. This is an operational
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
  owner. Only the separate capture root installs `ResumeReturn`. Context
  substitution preserves these nesting/completion clauses, including requests
  from a bind suffix. Capture stops at selection and omits that handler's
  wrapper. Suspension rebuilds unfinished frames with current resolved slots;
  re-entry repeats the activity cases rather than replaying stale completion
  actions. Current-state threading establishes clause 5; fresh handler
  wrappers recompute eligibility without renaming retained evidence.

Ordinary sequencing and adapter/force sequencing contribute `Bind`, calls
contribute `Owner`, and shallow forwarding contributes `ForwardHandler`;
selection supplies the capture bound. These constructors exhaust the saved
control contributed by the declared ordinary descriptor operations, while
the primitive cases above cover their value/store/request steps. Induction
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
return. Independent closure review of this repair has not run: launching a
fresh reviewer and restarting existing reviewers both failed with the tool's
`agent thread limit reached` error. Initial conformance review found no
authority violation. These facts do not certify the repaired theorem.

A related control obligation remains explicit. A pending handler search may
run an effectful guard. If that guard suspends, an outer handler may unwind
the candidate handler, and a forwarded source wrapper may later instantiate
a fresh handler occurrence. The pending search's candidate reference must
then either be a still-live exact occurrence or resolve to the current
source-prescribed occurrence; a stale expired handler ID cannot be selected.
The present owner-slot map alone does not specify that handler-control
reference transition. Resolve it from the common handler/search control
relation, including whether the candidate is active during the guard phase,
and prove it with the context reconstruction invariant. This is a primary
proof obligation, not an independently established source counterexample or
a new callback rule. Consequently the guard/search case above and the full
decorated-kernel preservation theorem remain unclosed.

The four saved-context constructors, source suffix labels with typed
environments, owned/borrowed pending frames, control environment links and
the separate root `ResumeReturn` have bounded record fields. Entry traverses
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
