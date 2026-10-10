# Full mixed Effect algebra: an exact bounded-active quotient and its boundary

Date: 2026-10-10
Status: producer-frozen, unreviewed research; complete mixed/source decision remains open
Role: adversarial algebra producer, not an independent reviewer
Baseline: `f75c8d2fc27c8e5f61e13632b234d56314d2a62c`
Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive persistent lease: this note
Supporting scratch: `/workspace/scratch/15155572c47b/mixed_total_attack/`

## 1. Result, scope, and remaining task

This lane proves a new exact decision construction for an unguarded mixed
recursive algebra class. It permits arbitrary independent binary replay,
explicit shared-child copying, recursive swap and both-from-right, raw prefixes,
raw right suffixes, and actual directed mix. It permits positive active PUSH
counts and arbitrarily many PUSH occurrences in recursive derivations.

Its structural hypothesis is that every constant left word and every fixed
prefix has **nonpositive PUSH-minus-POP displacement**: leaf `(p,n,r)` has
`p>=n`, and prefix `(a,b)` has `a>=b`. No restriction is placed on right debt.
This is a mathematical subcase, not a proposed source-language policy and not
a derived invariant of the source compiler. In particular an ordinary `P_1`
constant violates the hypothesis.

In this class active counts remain bounded by a directly computed `N`, while
debt counts need not be bounded. The correct coordinates are

```
d=p-n >= 0,   0<=n<=N,   r>=0.
```

For any `K>N`, retaining exact n and replacing d and r by `min(count,K)` is
an **operation congruence**. This yields a finite exact least-fixed-point
algorithm for the recursive grammar. The finite quotient retains joint tuples
and explicit child sharing. It also supports every fixed finite mixed future
context, including contexts containing positive PUSH displacement, for exact
active counts, pending presence, identity, local compact entry presence, finite
constant debt thresholds, and actual finite family/filter observations at every
future-context node.

A separate invariant rules out a naive one-ID independent two-string scaler.
For diagonal input `(q,q,0)`, every fixed mixed context has active count at most
`q+C`, where C is its fixed syntactic PUSH mass. Leading debt can nevertheless
be independently doubled while active count is retained. The asymmetry is real.
It does not establish decidability or undecidability for unrestricted mixed
recursion.

No genuine unguarded Minsky/PCP reduction is obtained. The complete algebra
with positive-displacement recursive suppliers remains unresolved. No source
realizability, contextual self-edge erasure rule, production algorithm, runtime
overflow argument, or complete Effect gate is certified by this note.

## 2. Supplied exact algebra

For one authentic identity and natural counts, use raw `W=(p,n,r)` with left
word `POP^p PUSH^n` and right word `POP^r`. Left composition is

```
(p,n) o (q,m) = (p+max(q-n,0), m+max(n-q,0)).
```

Replay performs this composition, sums the two right counts, and then applies
directed mix. Mix is identity if right debt or the left word is absent.
Otherwise, for the participating raw triple:

```
n>r:   mix(p,n,r)=(p,n-r,0)
n<=r:  mix(p,n,r)=(0,0,p+r-n).
```

The remaining operations are

```
swap(p,n,r)=(r,0,p)
both(p,n,r)=(r,0,r)
prefix(a,b)(p,n,r)=(a+max(p-b,0), n+max(b-p,0), r)
suffix(c)(p,n,r)=(p,n,r+c).
```

Prefixes and suffixes stay raw. A both result can have two pending sides. No
operation is eagerly mixed, reassociated, or replaced by an undirected sum.
The equations are the supplied research algebra in
`tools/research_mixed_debt_observer.py`; this lane does not independently derive
them from the pinned Oracle. The full finite-observer interface in
`tools/research_recursive_push_observer.py` is a read dependency, not an
implementation of the new recursive quotient.

The grammar is finite, with finite production expressions and finite derivation
trees. Ordinary child references choose independent derivations, even when
they name the same nonterminal. A production `let t=T in E(t)` chooses one
complete value of T and substitutes it in every bound occurrence in E. This
introduces correlation, not coordinatewise selection. There are no enabling
guards, arithmetic predicates on productions, or pruning by failed observations.

## 3. Nonpositive displacement is preserved and active counts are bounded

Assume every constant has p>=n and every prefix has a>=b. Put

```
N = max({0} union {leaf n} union {prefix b}).
```

This maximum is over the finite grammar syntax. It does not depend on recursive
depth, derivation size, independent child choices, or copying multiplicity.

Rewrite each value as `(d,n,r)` with `p=n+d`. For left composition, direct
substitution into the exact equations gives

```
d0=d1+d2
n0=max(n2,n1-d2)
r0=r1+r2.
```

The n formula uses the full joint pair. It follows from
`n2+max(n1-(n2+d2),0)=max(n2,n1-d2)`. Since d2>=0, n0 is at most
`max(n1,n2)`. Thus replay before mix preserves d>=0 and n<=N.

In these coordinates participating mix is

```
n>r:   (d+r,n-r,0)
n<=r:  (0,0,d+r).
```

In the second line the output coordinates are again `(d,n,r)`: its left
coordinates are zero and its right coordinate is d+r. If either original side
is absent, retain `(d,n,r)` unchanged. Mix never increases n and preserves
nonnegative d.

The raw operations become

```
swap(d,n,r)=(r,0,d+n)
both(d,n,r)=(r,0,r)
prefix(a,b)(d,n,r)=(d+a-b,max(n,b-d),r)
suffix(c)(d,n,r)=(d,n,r+c).
```

Prefix preserves d>=0 because a>=b. Its active count is at most `max(n,b)`,
which is at most N. Swap and both drop n. Suffix and identity retain n.
Constants satisfy the bounds by hypothesis. Induction on finite derivation
trees proves `d>=0,n<=N` at every actual syntax node, including raw nodes and
every intermediate production occurrence. Independent children and explicit
sharing both obey the same induction; no equality of their values is assumed.

The bound is compatible with unbounded syntactic PUSH mass. For example

```
T -> (1,1,0) | replay(T,T)
```

can have arbitrarily large finite derivation trees containing many actual PUSH
leaves, yet its exact active result is always 1. A shared version also permits
unbounded replicated leaf mass. Prefix `(1,1)` can occur recursively, and
arbitrary mixed swap/both/right-suffix cycles may be added without invalidating
the bound if the structural assumptions remain satisfied. This is not the
old grammar assumption that every recursive value has n=0.

## 4. The finite quotient is a true congruence

Fix any integer K>N and define

```
pi_K(d,n,r)=(min(d,K), n, min(r,K)).
```

The quotient carrier is the finite set
`{0,...,K} x {0,...,N} x {0,...,K}`. Its K entries mean counts at least K;
they are not claims that those counts equal K in the concrete algebra.

Each abstract operation evaluates the exact displayed d-coordinate operation
on the representative tuple and caps the resulting d/r coordinates again.
For every admitted operation F, including independent binary replay, the claim is

```
pi_K(F(W1,...,Wj))
  = pi_K(F(pi_K(W1),...,pi_K(Wj))).
```

Here a quotient tuple is converted back to raw p by `p=n+d` before using a
raw p-coordinate implementation. **Clipping p instead of d is not this theorem.**

Proof, covering every branch:

* Natural addition commutes with saturation:
  `min(x+y,K)=min(min(x,K)+min(y,K),K)`.
* In left replay, d0 and r0 are additions, so their saturated results agree.
  The only non-additive quantity is `max(n2,n1-d2)`. If d2<K its value is
  unchanged. If d2>=K, both d2 and its representative exceed N>=n1, so the
  result is exactly n2 in both cases. Consequently n0 agrees exactly.
* Mix's zero tests are unchanged by pi_K. Its active-versus-right comparison
  is unchanged as well: right debt below K is exact, and debt at least K is
  strictly greater than every possible n. In the surviving-active branch the
  participating r is below n<=N<K and is exact; output n-r is exact and d+r
  commutes with saturation. In the pure-right branch output r=d+r commutes
  with saturation. In either single-sided branch the operation is identity.
* Swap uses r unchanged as its new d, zero n, and d+n as its new r. Addition
  commutes with saturation. Both copies precisely the same saturated r into
  its two debt coordinates, preserving their correlation.
* Prefix's d output is d+(a-b), a nonnegative increment. Saturation commutes
  with that addition. For `max(n,b-d)`, if d<K it is exact; if d>=K>N>=b,
  both evaluations give n. This establishes the raw prefix result without
  mixing it. Suffix adds a nonnegative constant to r; identity is immediate.
* Constants have a single quotient value. Applying their quotient does not
  create extra choices.

This proves all primitive cases. Structural induction proves the same equation
for every production expression. For a shared child, use the *same whole*
quotient tuple at all occurrences; the induction is then a function-composition
argument. For independent children, apply it separately to each chosen tuple.
It does not replace a diagonal choice by an independent Cartesian product.

## 5. Exact recursive fixed point and observations

Assign a set of quotient tuples to every nonterminal, initially empty. Repeatedly
evaluate each finite production in the quotient and add its output tuples. A
reference reads its nonterminal set independently. A let production enumerates
one tuple in its supplying nonterminal and evaluates its entire body with that
tuple bound at every occurrence. Stop when a complete pass adds no tuples.

The carrier and grammar are finite, and additions are monotone. There are at most
`number_of_nonterminals * (K+1)^2 * (N+1)` distinct set additions. Therefore
the algorithm terminates without a depth cutoff or debt approximation.

Its final sets are exactly the images under pi_K of the actual finite-derivation
value sets. Soundness follows by induction on derivations using the congruence.
For the converse, every tuple added at a finite stage has actual finite child
witnesses by induction on the stage and production construction. For a bound
child select one witness and reuse it at every bound occurrence. Applying the
actual production to these witnesses has the recorded quotient output. Thus
there are no abstract tuples without concrete witnesses, including for sharing.

For observations on supplying nodes, exact n, p>0, r>0, p+n>0 and identity are
directly recoverable: `p=n+d`, and saturation preserves zeros. A fixed finite
constant threshold T on p or r is recoverable by choosing K>max(N,T). If a
count is at most T it is exact; otherwise its representative is still greater
than T. Finite Boolean combinations of these observations are consequently
decidable. This includes active equality to any natural input constant.

Finite family/filter decoration can be carried jointly with every count tuple,
provided its domain and all decoration transfers are explicitly finite and
exact. A terminal head subtraction updates the finite family decoration before
the actual local check. An active/filter violation is evaluated at that node
using exact n and its actual decoration. Neither observations nor failures
remove productions or prune supplier values. A parameterized family domain,
residual gamma allocation, source ID registration and an unbounded endpoint
domain are separate premises, not supplied by this arithmetic quotient.

If a production has a fixed local observation template over its children, an
existential violation at some production occurrence is decidable by querying
each productive, root-useful production with its actual independent/bound
child choices. Usefulness is computed from the finite unguarded grammar. A
local witness embeds in a complete root derivation because its other required
children are productive. A violation in a root derivation appears in one of
these templates. This proves bad-node existence and universal absence of a bad
node. It does not prove existence of a derivation satisfying guards at all nodes
under different, guard-pruned semantics.

## 6. Arbitrary fixed future contexts: exact bounded observations

The supplier hypothesis need not hold in a fixed finite future context. Such a
context may contain P_1, arbitrary finite full-pair constants, arbitrary fixed
raw prefixes/suffixes, swap, both, mix, bracketed replay, and repeated shared
or independent supplier selections. It can observe every actual syntax node.

Let m be the number of supplier-hole occurrences after expanding finite local
bindings, h the number of internal operation occurrences, B its syntactic PUSH
mass (leaf active counts plus prefix b counts, counted per occurrence), and

```
M=B+m*N.
K=max(N+1, T+(2*h+1)*M+2).
```

T is the maximum finite constant debt threshold in the requested observations;
use T=0 for pending presence/identity/entry predicates. M bounds active counts
at every context node: replay and prefix can only combine existing active
counts and fixed PUSH mass, while mix/swap/both never create active mass.
Repeated holes are counted with their actual multiplicity even though their
choices may be shared.

Saturate the supplier grammar at this K. Evaluate the entire context on chosen
quotient representatives, converting `(d,n,r)` to `(d+n,n,r)` at each hole.
Do not re-cap arbitrary context intermediates. The context is finite and its
representative arithmetic is exact. Its n at every node is the actual n, and
its p/r comparisons with every constant at most T are the actual comparisons.

Here is a finite-context precision proof, rather than an assumed extension of
the grammar congruence. Call two raw triples L-equivalent when their n counts
are equal and, separately for p and r, the coordinates are either exactly equal
or both strictly greater than L. At a hole the actual value and its quotient
representative are (K-1)-equivalent. At a constant they are identical.

If active counts in a subtree and prefix PUSH constants are bounded by M,
and input triples are L-equivalent with L>=2M, every primitive operation
produces triples whose active counts agree exactly and whose debt coordinates
are (L-2M)-equivalent:

1. For prefix, a differing p exceeds L>=b in both evaluations. It contributes
   no extra active PUSHes, and its debt result exceeds L-b. Exact small p values
   give identical results. Suffix adds debt; swap and both copy or discard debt
   and drop n. They do not lose precision beyond this bound.
2. For left composition, n0 is exact because comparing p2 with n1<=M either
   uses an exact p2 or concludes both large p2 values exceed n1. A differing
   p0 contains some large input debt with at most n1 subtracted and hence
   remains greater than L-M. Summed right debt is L-equivalent.
3. Mix's emptiness guards agree. A differing right count exceeds L>=M, so
   both executions take its non-active branch. Otherwise right count and the
   active/right comparison are exact. Active output therefore agrees. Any
   differing debt that survives or moves to the right has at most M active
   PUSHes subtracted. After the possible preceding left-composition loss its
   magnitude remains greater than L-2M. Discarded debt coordinates are zero
   in both executions.

At a binary operation use the smaller of its children's precision levels.
Induction up the finite tree loses at most 2M per internal node on a path.
The chosen K leaves precision greater than T (indeed at least T+M+1) at every
node and leaves enough precision to justify each guard. Thus every n count and
every requested finite constant debt comparison agrees at every syntax node.
For M=0 there is no active cancellation and the same proof has zero loss.

Each chosen quotient supplier tuple has a concrete witness. Conversely every
concrete supplier choice has its quotient tuple. Reusing one quotient tuple for
a shared hole preserves the observation result of every actual witness in that
class. Independent holes enumerate independent tuples. Consequently finite
enumeration of all quotient choices decides exact existence of the requested
future-context trace observations. Universal pass is absence of a violating
trace, with finite family/filter decorations updated at the actual nodes.

This theorem covers finite constant thresholds, including p=c or r=c for an
arbitrary finite query constant c. It does **not** cover unrestricted comparisons
of two unbounded debt coordinates, such as p=r between two supplier choices.
Two unrelated very large counts may have the same saturated representatives
while their equality differs. Treating that relation as a source observation
would require a separate proof.

## 7. One-ID diagonal obstruction and selective leading-debt scaling

Consider any fixed finite mixed expression E, allowing arbitrary natural
constants and positive-displacement prefixes, with each named input supplied
the diagonal `D_q=(q,q,0)`. Let C_E be its syntactic constant PUSH mass after
finite binding expansion. Then

```
active(E(D_q)) <= q+C_E
active(E(D_q))-left_POP(E(D_q)) <= C_E.
```

Proof by structural induction: a diagonal input has active q and displacement
zero; a constant's active and positive displacement are at most its PUSH mass.
Prefix increases active by at most b and displacement by b-a. Suffix preserves
the left pair. Swap/both output active zero and nonpositive displacement. Mix
decreases active while preserving p, or produces zero left coordinates.

For replay before mix, signed left displacement adds exactly, so its upper
bound is C1+C2. Also `p2>=n2-C2`. Therefore

```
n0=n2+max(n1-p2,0) <= max(n2,n1+C2) <= q+C1+C2.
```

Mix preserves both upper bounds. This proves every branch, including raw
intermediates, correlated copies, and independent occurrences all assigned the
same diagonal input. The result is not based on a count-width bound.

Consequently no fixed expression can implement independent active doubling
`(p,n,0)->(p,2n,0)` on all full pairs: choose p=n=q>C_E. More generally it
cannot implement n multiplied by any fixed factor greater than one on the
entire diagonal. This blocks the naive one-ID encoder that independently
scales two arbitrary natural coordinates as two word codes.

Leading debt behaves differently. For a left-only W=(p,n,0),

```
swap(swap(W))=(p,0,0)
replay(swap(swap(W)),W)=(2p,n,0).
```

This uses one explicitly shared W. Adding further projected copies scales p
by any positive integer while preserving n. When n>=p, k shared unprojected
copies instead yield `(p,kn-(k-1)p,0)`. Combining these constructions gives
triangular affine maps, not two independent scalers of p and n. An arbitrary
word-code reduction through that triangular family was not proved here.
The diagonal invariant is a limitation of a proposed construction, not an
impossibility theorem for all one-ID reductions.

## 8. The internal zero-test branch does not itself enable productions

There is a useful exact separator for `E(x,y)=(x+2,y+1,0)`. Define

```
J(W)=swap(mix(suffix(1,W)))
Z(W)=replay(J(W),P_1).
```

For y=0, mix transfers the pure residual `(x+2)` to the right, so J is
`L_(x+2)` and Z reconstructs E(x,0). For y>0, active survives mix, swap
drops it, and J is `R_(x+2)`; thus Z is `R_(x+1)`. All cases follow the actual
mix inequality, including its equality branch.

This detects zero by orientation while preserving the other magnitude on the
valid branch. It does not implement an enabling guard. The invalid branch is
still a derivation, and its debt is not necessarily an absorbing error. Apply
`W->replay(W,P_1)` exactly x+1 times to `R_(x+1)` to obtain identity; once
more obtains P_1. A proof that terminal activity excludes all such invalid
traces would therefore need an additional invariant over every allowed
instruction context. None was obtained here.

The older guarded-machine reduction cannot be imported as an unguarded
impossibility theorem. The new finite quotient likewise cannot be generalized
by simply asserting d>=0 when a positive-displacement leaf or prefix is present.

## 9. Verification and precise dependency boundary

Two lightweight Python probes ran under 30 seconds and 256 MiB each:

```
timeout 30s bash -c 'ulimit -v 262144; exec python3 -B /workspace/scratch/15155572c47b/mixed_total_attack/check.py'
timeout 30s bash -c 'ulimit -v 262144; exec python3 -B /workspace/scratch/15155572c47b/mixed_total_attack/check_future.py'
```

First probe: PASS, 44,884 quotient operation comparisons for N=3,K=4;
196 raw state tuples with d,r in 0..6 and n in 0..3, all binary state pairs,
all four unary cases, prefixes b in 0..3 and a in b..6, and suffixes 0..6.
Also 13,651 diagonal-invariant checks over 803 finite terms and q in
0..15 plus `10^20`; 3,212 independent literal-token comparisons; 400 selective
p-scaling cases; 100 exact separator/rehabilitation cases. Random term syntax
seed 314159, maximum generated depth 5. Internally measured wall 0.275046 s,
user CPU 0.315986 s, system CPU 0.003943 s, maximum RSS 11,704 KiB.

Second probe: PASS, 29,088 whole-future-context trace comparisons over 202
finite terms, N=3,T=2. For each expression its proved K was computed; supplying
d/r independently took values 0,1,K-1,K,K+1,2K+3 and n took 0..3.
Every actual syntax node compared exact n, p/r thresholds through T,
compact entry presence and identity. Random term syntax seed 271828, maximum
generated depth 4. Internally measured wall 0.416204 s, user CPU 0.452753 s,
system CPU 0.014943 s, maximum RSS 13,080 KiB.

No third probe, omitted range, timeout, killed process, Cargo/build/compiler
test, formatter, Git operation, child agent, source mutation or production
mutation. Both probes share the supplied algebra premises with the imported
count operations. Literal checks use the independently expressed token
evaluator but share those semantic premises. These are bounded consistency
checks, not source/Oracle certification or independent mathematical review.
The quotient, fixed-point and context extension claims are proved above for
all admitted counts/derivations; random finite terms do not supply that proof.

Read dependencies are the repository AGENTS and the design-authority,
orchestration-budget, research-lab and git-concurrency rules; the assigned
recursive-push algebra/observer and bracketed-replay obstruction notes; and
the two supplied research observer tools. No external theorem or niche
mathematical fact is required for these elementary algebraic proofs, so no
external research citation is used.

Changed persistent path: exactly this note. Scratch checkers are supporting
evidence outside the repository commit lease. Dependency hashes and this
artifact's freeze hash are reported separately to the primary so that the
artifact need not contain its own hash. Independent review remains pending.

## 10. Integration packet and honest next gate

Suggested research-only checkpoint subject:
`research: decide nonpositive-displacement mixed Effect grammars exactly`.
Only this leased note is a commit candidate. Baseline and Oracle are pinned
above. Shared task/theory/index records are intentionally deferred to the
primary; no production or authoritative source-contract file was changed.

The constructive gate ready for independent review is: finite mixed grammars
with p>=n constants and a>=b prefixes admit the exact d/r saturation algorithm,
including arbitrary recursive mix, raw suffix, swap, both and shared children,
and arbitrary finite future contexts with the observations stated in section 6.

The complete gate stays open for positive-displacement recursive suppliers,
unbounded family/endpoint formation, actual source realizability and contextual
self-edge erasure. Source use needs an independently established structural
certificate for each supplier component or another construction for components
that fail it. The theorem must not be turned into a restriction that rejects
ordinary source effects merely to simplify the proof. The diagonal obstruction
and failed zero-test separator supply exact limitations for two proposed
reductions; they do not establish impossibility of the requested complete
decision algorithm.
