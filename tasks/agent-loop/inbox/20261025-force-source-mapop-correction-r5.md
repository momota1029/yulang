# MAPOP-CAPTURE-RESPONSE — narrow correction to P

Status: FROZEN source derivation; independent delta review pending.
Author/runtime identity: `/root/force_mapop_correction_r5`. Sole write lease:
`tasks/agent-loop/inbox/20261025-force-source-mapop-correction-r5.md`.
No descendants. Requested Sol/high; observed model/effort UNKNOWN.

Objective/method: transcribe the accepted operation-mapper rule, derive its
continuation typing, and use symbolic discriminators against the rejected
simplifications. This supersedes only P section 5's matching-mapop equation,
its accompanying interpretation, and its unconditional response-type claim
(lines 323–338). Original P bytes remain unchanged; all other candidate
representations and open premises retain their existing status.

Baseline supplied by the frozen P receipt:
`9b945b0bb175e8e0919d388dc720babbdf0c2464` (no Git command run here).
Dependencies checked before writing:

| Input | SHA-256 |
|---|---|
| r5 contract | `88b5f57c9606dc0cd6d27731a7f9aafc127aa14e2715cde261eff2ffc27fd13a` |
| Operational paper | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| F report | `a849f178fbc55eb653c2fc4295e4b4675935e7c904cbef7da5100edb0b983212` |
| P report | `d7f8853e07cf2ec73fb99d3cbe045f3ab5b2e6f5626469417648a9fbfc313f88` |

## Exact source equation and typing

The authority is operational-paper lines 694–719. Write A/B for its source/
target type-argument vectors and T for the continuation's final result type.
Assume the same operation family/member o, syntactically well-typed adapter
code `a : P_o(A) -> P_o(B)` and `r : Q_o(B) -> Q_o(A)`, payload
`p : P_o(A)`, and `K = cont(U,x.N) : Kont(Q_o(A),T)`.
Thus, under its saved binders, `x : Q_o(A) |- N : T`.

First alpha-convert saved owner/handler binders U to U0, avoiding the free
names of the inserted adapter code and its environment. Apply that alpha
action only to the saved bound occurrences of N, yielding N0. In particular,
a free name of r that happened to spell an old binder stays free. Choose
fresh lexical binders z, z', p' and use capture-avoiding substitution.
Then the matching request step is exactly:

```text
mapop_w Req(q[o,A], p, cont(U0,x.N0))
  -> let p' <- a(p) in
       Req(q[o,B], p',
           cont(U0,z. let z' <- r(z) in mapop_w N0[z'/x]))
```

The outgoing payload has type `P_o(B)`. The new continuation accepts
`z : Q_o(B)`; `r(z)` returns `Q_o(A)`; substitution restores N0's original
input typing; `mapop_w` preserves its final returned value type T because
`mapop_w(Ret v) -> Ret v` and the matched signatures/adapters have the cited
syntactic typing. Consequently the wrapped continuation has
`Kont(Q_o(B),T)`. Its input changes from `Q_o(A)` to `Q_o(B)`; its final result
type remains T. This is a local typing derivation under the stated premises,
not a complete preservation proof for the language or arbitrary raw requests.
Malformed adapters/requests are outside this typing claim.

The response computation is `let z' <- r(z) in mapop_w N0[z'/x]`, with r's
computation outside the same recursive mapper. The payload computation a(p)
is likewise outside. Neither adapter creates a handler source grant.

On each resume of the new continuation, freshen U0 exactly once in its saved
body, then substitute the current caller's response for z. Alpha-conversion
at construction prevents capture; it is distinct from allocating the one
fresh owner/handler instance at resume. Do not define the wrapper through an
inner `Resume(K,...)` that repeats freshening of those same saved binders.
The free adapter environment remains free under this saved-name action.
These conditions follow lines 708–715 together with the resume rule 460–483.

For a nonmatching request `Req(q[c,C],p,Kc)` with
`Kc = cont(V,y.L) : Kont(Q_c(C),T)`, the distinct propagation rule is:

```text
mapop_w Req(q[c,C],p,cont(V0,y.L0))
  -> Req(q[c,C],p,cont(V0,y.mapop_w L0))
```

Here V0/L0 denote the analogous capture-avoiding alpha conversion against w's
free environment. This request's identity, payload and response interface
`Q_c(C)` stay unchanged; its continuation reinstalls the mapper so later
matching requests are still transformed. No a or r is inserted for this
nonmatching request (paper 712–716).

## Scope of a frame invariant

The plain syntactic framing operation
`cont(U,x.N) -> cont(U,x.mapop_w N)` retains input Q when it is a well-typed
framing of an existing `Kont(Q,T)`; the nonmatching propagation above is such
a case. Other ordinary request-propagation frames retain the particular
request's Q only under their own typing and capture premises. An outer frame
may change the final result type, as the handler example at paper 453–457
already illustrates; no universal final-result invariant is asserted.

Matching mapop is an interface-changing request transition. It cannot be
represented by P's bare `extend(K,mapop(w))` plus unconditional unchanged Q.
Even if `Q_o(A)` and `Q_o(B)` happen to coincide, omitting r still changes the
selected semantics unless r's identity behavior is separately established.
A chosen frame representation may claim a suffix-append equation for matching
mapop only after defining an adapter-bearing saved constructor whose plug
operation produces the exact let/r/mapop body above, with the appropriate
input-index change. This report adopts no such representation and proves no
unqualified `frames(K') = frames(K) ++ [saved(mapop(w))]` equation.

## Symbolic falsifiers and coverage

These are source/typing discriminators, not executed tests. The independent
oracle is the pinned paper equation; no candidate transition checker is used.

* Interface/direction/omission: choose `P_o(A)=Unit`, `P_o(B)=Bool`,
  `a(())=true`, `Q_o(A)=Nat`, `Q_o(B)=Bool`, `r(true)=0`, `r(false)=1`, and
  `N=Ret x`. The outgoing request carries Bool payload and a
  `Kont(Bool,Nat)` continuation. Keeping `Kont(Nat,Nat)`, omitting r, or
  reversing r's direction fails this typing instance. Reversing a cannot
  accept the original Unit payload.
* Same-input-type omission: let both response types be Nat and `r(n)=n+1`.
  With `N=Ret x`, response 0 must return 1. Bare mapop framing returns 0.
* Capture: let U contain owner u and let r refer freely to that same spelling
  u. Without pre-insertion alpha conversion, resume renames this free owner
  along with saved u. With `u -> v` first, N0 uses saved v and r retains free u.
* Double freshening: a saved owner v used in N0 must get one branch instance
  v1 per resume. A wrapper plus inner Resume which independently freshens the
  same saved owner allocates v1 and v2 and breaks that single-action equation;
  it can disagree with a response's saved-name interpretation or observations.
  This falsifies that definition pattern, not every nested Resume on distinct
  continuation binders.
* Self-transformation: choose r whose computation emits a matching q[o,A]
  request before returning a `Q_o(A)` value. The cited rule lets that adapter
  request run outside this same mapper. Mutating the body to
  `mapop_w (let z' <- r(z) in N0[z'/x])` transforms it to q[o,B] as well,
  changing the observable request and potentially recursively wrapping r.
* Nonmatching omission: take q[c,C] nonmatching, with L emitting q[o,A]
  after its response. Dropping mapop around L loses the later required
  transformation. Applying a/r to the initial q[c,C] changes its interface.

No seeds, bounded ranges, runtime traces or exhaustive search are claimed.
No Lean/code/tests/builds/Git/scratch files were used. CPU and memory are
unmeasured; elapsed wall time UNKNOWN, so charge the full 100-second grant.
The derivation is limited to this source-rule correction. O-NORM, O-RESULT,
source-to-Lean correspondence and parent theorems remain OPEN.

Recommended next action: fresh independent delta audit against these exact
bytes and the pinned paper; only then consume P with this narrow correction.

Commit packet: exact leased path is the file named above; baseline is the
pinned SHA above; no dependency hash changed; review PENDING; checks performed
are source reads and dependency SHA-256 equality only. Proposed message:
`research: correct captured mapop response adaptation and input typing`.
Shared-record deltas intentionally left to Luna: record STOP/frozen digest,
charge 100 seconds, dispatch the reserved delta review, and retain all parent
open gates. STOP: no further writes after this artifact's digest receipt.
