# Exact observers for cyclic debt derivations with finite mixed continuations

Date: 2026-10-10
Status: independently reviewed mathematical theorem for the stated debt-grammar/finite-observer interface; source and production closure excluded
Role: M3 research production, not certification or production implementation
Baseline: `e2f29d0a30f81616b4963cb1b2a42d9a798af2b3`
Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Lease: this note and `/workspace/scratch/15155572c47b/mixed_construct/`

## 1. Result

There is an exact terminating observer for a finite cyclic one-ID **debt
grammar**, followed by an arbitrary fixed finite bracketed operation context
that may introduce PUSHes. The debt grammar may contain arbitrary cycles,
binary replay, swap, both-from-right, POP prefix and suffix, and explicit copying
of one chosen derivation. In particular, it permits cyclic both/replay doubling,
and does not require that its exact output language be regular or context-free.

The continuation may use all these operations, PUSH prefixes and constant
PUSH-bearing weights, and may copy its supplied debt derivation any finite
number of times. The algorithm preserves the exact active PUSH count and both
debt-presence observations at **every continuation node**. It consequently
decides local fixed-family active/filter checks, insertion-time active checks,
and the local compact left-ID-presence predicate at their actual placement.
It is a decision theorem, rather than another finite grammar representation.

The finite observation domain depends on the finite continuation's actual PUSH
mass. No semantic count limit, source-input restriction, saturated arithmetic
semantics, complete registry, SAT prerequisite, or second production solver is
introduced. Exact cyclic derivation syntax remains available for later queries;
each new continuation receives its own exact observer.

The important boundary is explicit: this does not decide a grammar in which
PUSH-bearing contexts themselves occur on unrestricted recursive cycles. A
fixed finite continuation is a mathematical query interface, not a proposed
restriction on accepted source programs. Actual source correspondence must show
which source-owned cyclic region is debt-only and which subsequent consumers
are represented by a finite continuation. In particular, finiteness of IDs or
endpoint keys alone does not establish this decomposition.

## 2. Exact algebra and the debt fragment

Use one authentic identity with natural counts and initial fixed active family
S. Write W=(p,n,r), meaning left POP^p PUSH^n and right POP^r. Filters and
families are separately retained. All calculations below use the exact
natural-number lift, not Oracle u32 overflow or saturation.

The pinned owners are `crates/infer/src/constraints/mod.rs:3566–3612` and
`constraints/directed_weight.rs:12–39,137–176,399–420`. These supply:

```
left composition:
  p' = p1 + max(p2-n1,0)
  n' = n2 + max(n1-p2,0)

swap(p,n,r) = (r,0,p)
both(p,n,r) = (r,0,r)
left-prefix(a,b):(p,n,r) ->
  (a+max(p-b,0), n+max(b-p,0), r)
right-suffix(c):(p,n,r) -> (p,n,r+c).
```

Replay first applies left composition and sums right debt. Mix leaves a
single-sided input unchanged. If both the composed left word and right debt
are nonempty, it appends the right POPs: a surviving PUSH remains on the left;
a pure residual debt moves to the right; exact cancellation gives identity.
No associative flattening is used anywhere in the algorithm or proof.

A debt value is n=0, represented by (p,r). The debt fragment is closed under
all the listed operations except PUSH introduction. In this fragment:

```
swap(p,r) = (r,p)
both(p,r) = (r,r)
left-POP-prefix(a):(p,r) -> (p+a,r)
right-POP-suffix(c):(p,r) -> (p,r+c)
replay((p1,r1),(p2,r2)) =
    (p1+p2,0)                 if r1+r2=0;
    (0,p1+p2+r1+r2)           otherwise.
```

The replay equation includes empty operands. If the total right debt is
positive and the total left debt is zero, mix's single-sided guard already
gives the second result; if both are positive, mix moves their sum right.
Thus the equation is source-exact despite replay's nonassociativity.

The grammar is finite and denotes every permitted finite derivation tree.
Leaves are any finite debt constants. Productions are finite expressions of
the listed debt operations and nonterminal references. A production can bind
one chosen child derivation to a variable and use that variable repeatedly;
alternatively, repeated occurrences of a nonterminal may choose children
independently. Those two meanings remain distinct.

For a shared variable, the same actual child derivation supplies every use.
For independent occurrences, the production ranges over a Cartesian product
of child value sets. No correlation is inferred just because two references
have the same nonterminal name. This distinction matters for a continuation
such as replay(t,swap(t)).

## 3. A query-specific exact finite saturation

Let C be a fixed finite operation tree with holes supplied by debt values.
All its constants and primitive words are finite. Expand sharing in C into its
finite occurrence tree for the purpose of counting PUSHes, while retaining the
specified sharing of debt choices. Let B be the sum of all constant PUSH counts
in that expanded tree. A PUSH-bearing constant is counted once per evaluated
occurrence; a debt hole contributes zero. C may contain any finite number of
swap, both, prefix, suffix and replay operations.

Set M=B+1 and define

```
q_B(p,r) = (min(p,M), min(r,M)).
```

The marker M means "at least M", not a semantic value replacing all future
debt. The finite debt-observation domain has (B+2)^2 elements. Saturating
addition in this finite *query domain* is

```
x ⊕ y = min(x+y,M).
```

Evaluate every debt production with swap/both, clipped prefix/suffix sums, and
the displayed replay side rule. Clipping preserves zero exactly. For natural
x,y, min(x+y,M)=min(min(x,M)+min(y,M),M). It follows, by inspection of each
operation, that q_B is a congruence for the entire debt fragment:

```
q_B(op(W1,...,Wk)) = op_B(q_B(W1),...,q_B(Wk)).
```

This includes both's copying and the branch in replay; no cancellation occurs
in the debt fragment. Therefore arbitrary cyclic productions and unbounded
counts cause no obstacle to this particular finite saturation.

Maintain a subset A_T of this finite domain for each nonterminal T. Start all
sets empty. Repeatedly evaluate productions using currently available child
states and insert their results. For a bound/shared child variable choose one
state and reuse it at all references. For independent children choose each
state independently. Stop when no set grows.

There are at most |N|(B+2)^2 successful count-state additions. Each production
has finitely many arguments, so evaluating one complete round is finite. This
is termination without a numeric count cap or an iteration cutoff. If finite
filter decoration is retained, multiply this bound by the size of its finite
domain. No small or polynomial resource bound is claimed for the complete
query computation.

Soundness is induction on insertions: every inserted state is the image of
actual finite child derivations, and composing those derivations supplies a
finite parent witness. Under shared semantics the chosen witness is reused,
so correlation is preserved. Completeness is induction on finite derivation
height: all child images eventually occur, and their production inserts the
parent image. Hence the final A_T is exactly

```
{ q_B(W) | W is the value of a finite derivation of T }.
```

If desired, store one actual derivation witness for each inserted state. This
makes reported existential observations reviewable; it is not necessary for
the termination proof. Universal pass means every resulting query state
passes; existential violation means at least one does. Empty denotation is
recognized because its saturated state set remains empty.

## 4. Why the finite continuation is observed exactly

The saturated state is supplied to C as the ordinary finite representative
(p,0,r). Evaluate C with the exact natural-count operations and original
bracketing. **Do not clip intermediate mixed values after each operation.**
They are finite arithmetic values because C is finite. The resulting node
observations are exactly those of every actual input represented by that state.

Here is the invariant proving that assertion, including raw weights before
mix. For naturals x,y and K>=0, write

```
x ~_K y  iff  x=y or (x>K and y>K).
```

At a node v let b_v be its subtree's syntactic PUSH mass, and K_v=B-b_v.
Compare exact input evaluation W_v=(p_v,n_v,r_v) with representative evaluation
W'_v. The induction establishes

```
n_v = n'_v <= b_v;
p_v ~_(K_v) p'_v;
r_v ~_(K_v+n_v) r'_v.
```

The extra n_v in the right-debt threshold is necessary. Raw wrappers can
leave active PUSHes and pending right POPs together until a later mix; those
current PUSHes must remain available in the cancellation budget. Merely
relating both debts above K_v is insufficient as an inductive proof.

At a debt hole, b_v=0 and n_v=0; min(p,B+1) and min(r,B+1) agree with their
exact values unless both exceed B. Constant leaves agree exactly. Push counts
never exceed syntactic PUSH mass because none of the operations creates a PUSH
from debt; both copies only right POPs and swap drops PUSHes.

The elementary facts used below are: increasing K strengthens ~_K; adding
related nonnegative quantities preserves ~_K; and, if x ~_(K+a) y and
0<=c<=a, then max(x-c,0) ~_K max(y-c,0). Also x ~_K y with K>=c implies
max(c-x,0)=max(c-y,0). In the unequal case both inputs exceed c, so these last
equalities and relations follow directly; the equal case is immediate.

### Unary operations

Swap changes (p,n,r) to (r,0,p). The old right relation has threshold at least
K_v, and the old left relation has threshold K_v. Thus both new debt relations
hold after discarding the old pushes. Both changes the value to (r,0,r) and
the same reasoning applies to both copies. POP prefix/suffix adds a constant
to a debt without changing PUSH mass or n, preserving the relations.

For prefix POP^a PUSH^b, the child's budget is K_v+b. The incoming p relation
therefore compares identically with b. Its surviving new PUSH contribution
max(b-p,0) agrees exactly, and cancelling b from p preserves the new
~_(K_v) relation. The untouched right debt previously had threshold
K_v+b+n_child, at least K_v+n_new. Prefixing a fixed compound word uses its
normal form or repeats these primitive steps. The budget counts every actual
PUSH in its syntax, so reduction of a constant word only increases slack.

The source's right suffix takes only POPs from its supplied word. It adds no
PUSH and preserves the right relation. If an implementation chooses to count
discarded suffix PUSH syntax in B, that overestimate is also safe.

### Binary replay and mix

Write K=K_v and let child PUSH budgets be b1,b2. The children have remaining
budgets K+b2 and K+b1 respectively. Before mix:

```
p0 = p1 + max(p2-n1,0)
n0 = n2 + max(n1-p2,0)
r0 = r1+r2.
```

The p2 relation has threshold K+b1>=n1. Thus max(n1-p2,0) agrees exactly,
and n0 agrees exactly. The cancellation in p0 spends at most n1<=b1,
leaving p0 related at threshold K.

Each right child threshold is at least K+n1+n2: for r1 it is
K+b2+n1, and for r2 it is K+b1+n2. Consequently

```
r0 ~_(K+n1+n2) r'0,
```

which implies r0 ~_(K+n0) r'0. In particular, the comparison of r0 with n0
is identical and max(n0-r0,0) agrees exactly.

All guards in mix are also identical: p0/r0 zero versus positive follows from
their relations at nonnegative thresholds, and n0 agrees exactly. If one side
is empty, mix returns it unchanged, and the required relations hold. If both
participate and r0<n0, the result is (p0,n0-r0,0), with exact new n. If
r0>=n0, the result has no active PUSH and moves p0+r0-n0 to the right unless
it is zero; the residual right quantity is related at threshold K. Exact
cancellation is distinguished because the comparison and every relevant zero
test agree. This establishes the invariant in every mix case.

Every occurrence of a shared hole receives the same representative. The
induction remains valid when the same actual derivation supplies all those
holes: no step assumes independence. For independent holes, apply it to each
chosen actual input. One may use the same global B for multiple independent
debt grammars and enumerate their independent state choices.

At **every node**, K_v>=0. Therefore p/r zero and positive signs agree, and n
is identical. This proves equality of active counts, active presence, left
ID-entry presence p>0 or n>0, right presence r>0, total pending-debt presence,
and identity versus nonidentity. It proves more than a final active Boolean,
without claiming equality of unbounded residual debt magnitude.

## 5. Filters, residual families, and consumer placement

At fixed family S, a local active-stack check against F is violated exactly
when n>0 and S is not a subset of F. The theorem preserves n at every node.
Finite constant filters and the grammar's intersections may be carried as
exact decoration: the closure under intersection of finitely many specified
filters is finite; swap/both reset to All, insertion erasure resets to All,
and source prefixes/replay intersect their supplied filters. There is no
numeric approximation of these decorations.

Thus a filter check may occur before replay, after replay, before insertion
erasure, or at any other explicitly represented node. The algorithm uses its
actual position. It does not justify moving an insertion filter after replay.
The pinned source owners are `machine/bounds.rs:3174–3210,3213–3255,3285–3360`
and `machine/propagate.rs:11–60`.

Concrete positive-shape/future-lower checks also depend on the actual endpoint
and filter owner. This note preserves the same filter and schedules the same
local check for the supplied finite continuation, but does not reconstruct
those endpoints, registration owners, or future insertions from count state.
A registered future filter is retained as a real obligation, not dropped
because the present count has no active PUSH. The theorem supplies the count
part of such checks; it does not replace their source ownership argument.

Two additional local consumers follow directly:

* The inspected compact method's one-ID entry predicate is p>0 or n>0. It is
  exactly preserved, including pure leading POP. With fixed written heads and
  declared source facts, its head-retention formula is consequently preserved.
  This is the local method in `compact/collect/mod.rs:1019–1043`, using
  `StackWeight::contains` at `poly/src/types.rs:382–384`, not all public output.
* A terminal nullary-head consumer computes H from written heads and the
  active S (or All when n=0), then replaces S by S minus H without changing
  counts. Exact n and exact S determine this operation, so a following local
  filter or compact observation is exact. The actual source operation is
  `row_effect.rs:175–183,1190–1244`.

A finite continuation can retain deterministic family changes as exact finite
decoration and continue the same count proof: head subtraction never changes
counts, and swap/both discard active families. A later same-ID active-family
compatibility check must be evaluated using the preserved actual decorations;
it is not waived. If different active families would make source replay
inadmissible, that mismatch is reported identically. The initial fixed-family
theorem does not authorize replay of arbitrary unequal families.

No complete claim is made for gamma allocation keyed by exact residual debt,
residual endpoint incidence, whole support collection, generalization,
freshening, extrusion/intrusion, or solver rollback. Those consumers may need
the exact retained grammar or additional source invariants. Count-sign equality
does not silently decide an exact residual-weight key.

## 6. Scope demonstrated by formerly obstructing examples

The grammar T -> R_1 | replay(I,both(T)) denotes precisely R_(2^k). It is
within the theorem: clipping is a congruence for its debt operations, even
though its exact unary output language is not context-free. For continuation
replay(t,PUSH^b), B=b. Saturation retains exact debts <=b and one large
marker, deciding activity exactly for every k without enumerating k.

For the progression T -> R_1 | replay(T,R_4), it similarly decides every finite
mixed continuation on the infinite family R_(1+4k). The progression is only an
algebraic example in this note; source reachability and its actual recurrence
are assigned to the independent source lane and are not inferred here.

The query-specific domain is not a finite contextual congruence for all future
PUSHes. If a later query supplies a larger PUSH word, it receives a larger B
and a fresh finite saturation over the **original exact grammar**. Keeping
only the earlier clipped set and treating it as durable solver authority would
be unsound. Likewise a cyclic PUSH-bearing continuation has no finite B in
this proof and remains outside its scope.

This is a natural observation boundary rather than a numerical accepted-input
boundary. It supports arbitrarily large debt in any cyclic POP-only region,
arbitrarily large finite queries, and arbitrary bracketing/copying in both.
No source cycle is forbidden to obtain the result.

## 7. Verification and handoff

The bounded consistency probe is
`/workspace/scratch/15155572c47b/mixed_construct/check.py`. Its purpose is to
falsify implementation/proof accounting mistakes, especially mixed raw weights
and finite copies. Universal exactness
and termination rest on the congruence and PUSH-budget induction above, not on
bounded enumeration. No compiler or Oracle was executed.

Read-only source and note inspection used the assigned cone and pinned Oracle
objects. No production code, shared record, Git index/ref, or other leased
output was changed. No Cargo/build/compiler tests or children were used.
Shared task/theory/design updates are deferred to the primary. The theorem is
producer work and awaits independent mathematical review.

Suggested checkpoint subject: `research: decide cyclic debt grammar mixed observers`.
Remaining full gate: exact observation for unrestricted PUSH-bearing cyclic
bracketed grammars, or a source-derived decomposition that makes this debt
theorem sufficient for the relevant source consumer. Neither undecidability
nor full generic decidability is asserted.

One Python process ran successfully under a 30 s timeout and 256 MiB virtual
memory limit:

```
timeout 30s bash -c 'ulimit -v 262144; exec python3 -B /workspace/scratch/15155572c47b/mixed_construct/check.py'
```

Result: PASS. Reproducible seed 10102026; 539 finite contexts (500 sampled
depth-at-most-four trees and 39 dedicated contexts), 30,662 debt-input
comparisons, 182,588 per-node observation comparisons, 15,235 debt-replay
congruence checks, and 12 finite grammar saturations. Inputs include counts
0 through the local threshold where sampled, threshold/threshold+1/
threshold+2, and 1000+threshold; they are not an exhaustive test of all counts
or all contexts. Dedicated cases include shared holes, swap, raw PUSH/right-POP
weights, and PUSH budgets 0..12. Grammar checks use B in {0,1,2,5,13,50} for
the doubling and +4 progressions. Replacing the strict large marker B+1 by B
is rejected by the exact-cancellation versus residual-debt witness.

This probe uses the accepted algebra equations for both evaluations. It is a
bounded check of query abstraction and budget accounting, not an independent
Oracle or source-equation validation. Python process resource accounting:
user CPU 0.218494 s, system CPU 0.017604 s, internally measured wall
0.203432 s, maximum RSS 8,576 KiB. This is resource accounting for one short
run, not a performance benchmark. An initial wrapper command failed before
starting Python because `/usr/bin/time` was unavailable; the successful run
used Python's `resource` accounting. Total exploratory Python process count:
one. No omitted shard, timeout or unsuccessful Python run.

Direct note dependencies, final SHA-256 snapshot:

```
dacb7529e02f06ab38aa37ad88ca3c1e6544b4bb1eaea95e9331ce1e27c3aca3 contextual-effect-path-theorem
96f7c1545f9e4dbfef8c2190a8ca1b9849ee288c88fbb93e325737b36d33492a contextual-effect-counterexamples
33b332d25c68d9ab10620d4c5d94d367602617a816f3172f1ce716b58ad9b3dc bracketed-replay-decision-obstructions
7e0c48efdafe03a5c503c508c5706375382c0e1b3e9262e6b08c70c51dab0db4 correlated-mixed-replay-discriminator
a3918fab770a5e0e66d94eba3219142b7f5c1116e0c76ccf144b9140f59776b4 contextual-effect-source-correspondence
```

The artifacts are frozen at producer handoff. Exact persistent output is this
one repository note; the leased scratch checker is supporting bounded evidence.
All shared records and Git integration remain primary-owned.

## Independent mathematical review

The fresh `mixed_observer_referee` read-only pass checked producer snapshot
`e00a6db54fa05f5edbb75c7c87d1177e39a67b7de3851527874cc3f4ff3c0549`,
the auxiliary algebra argument, and the pinned operation/consumer owners.
It found no blocking or major defect in the exact debt quotient, least-set
saturation, asymmetric raw-state invariant, finite continuation simulation,
sharing distinction, or future-query reconstruction. This status applies to
the displayed mathematical interface and its local count/presence corollaries.
It does not assume source reachability, certify a production implementation,
or discharge unrestricted recursive PUSH-bearing contexts, residual keys,
generalization, transport, or rollback. Producer-era handoff statements above
remain historical provenance. This review used proof/source inspection and
hash verification, with no executable probe or compiler run.
