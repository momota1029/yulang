# Recursive PUSH replay: exact full-pair subcases and a guarded-model boundary

Date: 2026-10-10
Status: producer-frozen, unreviewed conditional research; no general decision theorem or source closure
Baseline: `e3ddf9f19e08be74a8467a61b5415244f6f5ac0f`
Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this note and `/workspace/scratch/15155572c47b/recursive_push_attack/`

## Result and honest remaining gate

This lane obtains exact observers for three **unguarded, recursive PUSH-bearing**
families with full left POP-then-PUSH pairs, including a nonlinear shared-child
cycle. Neither result depends on a finite recursive PUSH budget or debt clipping:

1. A linear cancellation cycle has a directly computed finite affine phase and
   an arithmetic signed tail, for arbitrary finite raw seeds.
2. A linear growth cycle keeps both leading POP and active PUSH counts unbounded.
   Its exact denotation is an affine ray in the full left pair.
3. A nonlinear shared-child replay cycle keeps positive leading POPs and active
   PUSHes, with exact active counts containing a geometric progression. Binary
   automata decide every fixed finite mixed observer of any finite selection of
   these values, including repeated shared selections and independent selections.

The statement covers exact counts and correlated observations at all nodes of
the finite observer. It does not decide observations at every node of arbitrarily
large recursive derivation trees, arbitrary mutually recursive tree grammars, or
the entire source solver. The finite observer is unrestricted in the supplied
operation algebra; the supplying recursive grammar is the explicit family stated
below. These are mathematical subcases, not proposed restrictions on supported
source programs. No maximality theorem is claimed.

A separate reduction proves undecidability if productions are augmented with
zero-test enabling guards. Those guards are **not** present in the assigned
`Grammar` class, and source rejection is not derivation pruning. The reduction
must not be used as an impossibility result for the actual unguarded task.

The general unguarded full-left-pair/right-debt problem remains unsolved by this
lane. The output is therefore a constructive partial advance and a sharply scoped
barrier, not full gate closure.

## 1. Exact model and observation construction

Use the assigned one-ID natural-count algebra, fixed family and All replay
filters. A raw value is `(p,n,r)`. The exact left composition is

```
(p,n) compose (q,m) = (p+max(q-n,0), m+max(n-q,0)).
```

Replay composes in the displayed direction, adds right debts, then mixes.
Mix is identity if either side is empty; otherwise it appends right debt to the
left word and either keeps a surviving active PUSH count on the left or moves
the pure residual to the right. Prefix `(a,b)` composes before the raw left word;
suffix adds right debt without immediate mixing. Swap is `(r,0,p)` and drops
PUSHes. Both-from-right is `(r,0,r)` and also drops PUSHes. No step reassociates
general replay or normalizes a raw wrapper before its actual mix point.

These are the operations in the frozen `tools/research_mixed_debt_observer.py`;
that tool deliberately rejects PUSH-bearing recursive grammars. This note
studies their exact algebraic extension and does not alter that tool or its
scope claim.

**Finite observer compilation.** For each syntax occurrence, introduce natural
variables for its three exact output counts. Impose the graph of the actual
operation. Every such graph is a finite Boolean combination of integer linear
equalities and inequalities. For example `z=max(x-y,0)` is

```
(x>=y and z=x-y) or (x<y and z=0).
```

Mix additionally branches on `p+n=0`, `r=0`, and whether the composed active
count exceeds right debt. These are also linear predicates. Thus the observer's
entire per-node trace is described by a finite Presburger formula, with all
bracketing and raw intermediates retained.

Introduce one input triple for each deliberately shared selection. Repeated
occurrences use those same variables. Independent references have separate
input triples, even if they name the same nonterminal. The observer graph itself
does not sample coordinates separately, and a both result uses the same `r`
variable in both copied positions. It follows that any supplying value set with
an effective Presburger definition supports exact finite-observer decision.
The nonlinear family below instead uses an effective binary-automatic predicate.

The resulting symbolic trace relation includes all exact active counts, leading
and right debt signs, local left-entry presence, and identity. It is not required
to enumerate infinitely many exact active counts. A query for one count, a
violating filter, or any Boolean combination is a terminating emptiness query
on that representation. Fixed terminal family subtraction and finite local
family predicates can be encoded as finite case choices without changing the
count graph. This is not a reconstruction of source registration, gamma keys,
freshening or whole compact collection.

## 2. Linear recursive PUSH cancellation with arbitrary raw seeds

Fix `a>=1`, `b>=0` and the single-child context

```
C(W) = replay(prefix(0,a,W), R_b),     R_b=(0,0,b).
T -> any member of a finite seed set | C(T).
```

Each traversal of the cycle introduces `a` actual PUSHes. Thus its recursive
PUSH mass is unbounded. Its exact denotation is the union, over the seeds, of
the full orbits `{C^k(seed) | k>=0}`.

Define the signed ray

```
Z(q) = (0,max(q,0),max(-q,0)),          q in Z.
```

The raw prefix of `Z(q)` is retained before replay. For `q<0` it is
`(0,a,-q)`, carrying active PUSHes and right debt simultaneously; it is not
normalized early. Direct use of the actual replay equation gives

```
C(Z(q)) = Z(q+a-b).
```

For a full left pair `(p,n,0)`, set

```
u = max(p-a,0),     v = n+max(a-p,0).
```

If `b=0`, the result is `(u,v,0)`. If `b>0` and `v>b`, it is
`(u,v-b,0)`; if `b>0` and `v<=b`, it is `Z(-(u+b-v))`.
In particular, while `p>=a` and `n>b`, the full active pair maps exactly as

```
(p,n,0) -> (p-a,n-b,0).
```

This includes genuine POP-then-PUSH states with `p>0,n>0`, rather than assuming
`p*n=0`.

Here is a complete closed orbit construction. Keep the raw seed itself at
index zero. Compute `W1=C(seed)` exactly once. This is mixed, hence identity,
pure L, pure R, or a full active left pair.

* If `W1.p=0`, set `s=1`, `q=W1.n-W1.r`. The entire remainder is
  `C^k(seed)=Z(q+(a-b)(k-s))` for `k>=s`.
* Otherwise write `W1=(p,n,0)`, where `n` may be zero. Compute
  `j=floor(p/a)` when `b=0`, and
  `j=min(floor(p/a), max(floor((n-1)/b),0))` when `b>0`.
  For `0<=t<=j`, the bulk phase is `(p-at,n-bt,0)` at index `1+t`.
  For `n=0,b>0`, `j=0`, so no invalid active step is taken.
* At its endpoint, if the leading debt is zero, use that endpoint as signed
  tail start. If leading debt remains positive, apply `C` exactly once more.
  The result has leading debt zero: either `p<a` makes the prefix's leading
  debt zero, or `n<=b` makes replay transport the pure residual to the right.
  Use that result as `Z(q)` and continue with the signed formula above.

The quotient/division calculations determine the bulk phase length directly;
they are not an iteration cutoff. The finite bulk phase itself may be retained
as one formula with a bounded integer parameter, rather than explicitly listing
an enormous number of seeds or transient values. The tail has one unbounded
integer parameter. Both formulas are Presburger-definable. The observer
construction in section 1 therefore decides exact finite mixed queries of any
finite number of these orbits, preserving sharing and independent selections.

For example `seed=(9,11,0)`, `a=2`, `b=3` gives

```
(9,11,0), (7,8,0), (5,5,0), (3,2,0), R_2, R_3, R_4, ... .
```

The active phase retains both left counts; right transport occurs at its exact
mix point. Changing `a-b` changes the tail's direction and can produce eventual
unbounded active PUSH depth instead of unbounded right debt.

## 3. A linear cycle with both left counts permanently unbounded

Fix `a>=0,b>=1`, and retain the bracketing

```
G(W) = replay(L_a, replay(W,P_b)),
L_a=(a,0,0), P_b=(0,b,0).
T -> (p0,n0,0) | G(T).
```

On any full left pair, including pure leading debt, the inner replay increments
the active coordinate by `b`, and the outer replay increments the leading
coordinate by `a`. Neither application has right debt. Consequently

```
G^k(p0,n0,0) = (p0+ak,n0+bk,0),       k>=0.
```

For `a>0`, both leading debt and active PUSH depth grow without bound. This
counterexample to a forced one-counter reduction is also an exact constructive
subcase: the entire supplying set is one affine ray, so section 1 decides its
finite observers without enumerating derivation depth. Recursive PUSH mass is
unbounded because the cycle explicitly introduces `P_b` on every traversal.

## 4. Nonlinear shared PUSH recursion with full left pairs

Fix `h>=1`, `x0>=1`, and set

```
A_h(x)=(h,h+x,0),                    x>=0.
T -> A_h(x0)
T -> let t=T in replay(t,t).
```

The recursive rule has two occurrences of one selected child. This is explicit
same-child sharing, not two independent references. Direct directed composition
gives

```
replay(A_h(x),A_h(y)) = A_h(x+y).
```

Indeed the leading count is `h+max(h-(h+x),0)=h`, and the active count is
`h+y+max((h+x)-h,0)=h+x+y`. Right debt is zero, so mix does nothing.
This is a proved subalgebra calculation, not an associative rewrite rule for
arbitrary directed weights.

Induction on finite derivations proves the exact denotation

```
{ A_h(x0*2^k) | k>=0 }.
```

Both leading and active counts are positive at every recursive value. The
total PUSH occurrence mass doubles with the child tree and is unbounded.
The active-count set is not semilinear: in one dimension any infinite finite
union of arithmetic progressions has bounded gaps in its eventual support,
whereas consecutive `h+x0*2^k` have gaps tending to infinity.

Independent references change the denotation. For `h=x0=1`, children with
active counts 2 and 3 replay to `(1,4,0)`; its displacement 3 is not a power of
two. A production `replay(ref(T),ref(T))` must therefore not use the diagonal
algorithm of the displayed `let` rule.

### Exact finite observer algorithm, including independent geometric selections

The property `Pow2(t)` holds exactly when the natural `t` is a positive power
of two. Encode natural numbers in binary, least significant bit first, allowing
zero padding. Its language is `0*1 0*`: a finite automaton remembers whether it
has seen zero, one, or more than one `1` bit, and accepts exactly one.

For each chosen supplying value, use a natural `t` and constraints

```
Pow2(t), p=h, n=h+x0*t, r=0.
```

Keep one `t` variable for each shared selection, and distinct variables for
independent selections. Combine these with section 1's exact per-node operation
graph and the requested observations.

This formula has an effective finite-automaton decision procedure. The essential
construction is given here, so the argument does not assume that ordinary
Presburger arithmetic permits variable exponentiation:

* The synchronous binary relation `x+y=z` is recognized with a carry state.
  At each digit, require `z_bit=(x_bit+y_bit+carry) mod 2` and update carry by
  integer division by two. Reject a nonzero final carry. Equality and constants
  have finite automata as well.
* Constant multiplication, such as `x0*t`, uses finitely many repeated
  additions and auxiliary tracks; `x0` is a fixed finite input constant.
  Signed coefficients in an integer linear equation are moved to its opposite
  side. Inequality uses an existential nonnegative slack variable.
* Intersections, unions and complements of synchronous regular languages are
  effective finite automaton operations. Existentially quantifying a track is
  nondeterministic projection. Arbitrary common zero padding handles witnesses
  with larger encodings; after projection, permit the removed trailing zero
  columns of retained tracks using the finite closure under such padding.
  Universal quantification is complement, projection, complement.
* Add each `Pow2` automaton by synchronous intersection. After projecting all
  auxiliary variables, decide emptiness by reachability of an accepting state
  in the resulting finite graph. Unconstrained trace/output tracks give a
  finite automaton representing all possible exact trace tuples.

All of these operations terminate because each automaton is finite. Thus the
non-semilinear active-count set does not prevent exact finite observation.
No bound on `k`, recursive depth, total PUSH mass or count size enters this
decision construction. The same proof works for a fixed `m>=2` copies of one
selected child, by using base `m` and the regular predicate `t=m^k`; the algebra
maps `A_h(x)` to `A_h(mx)`. A union of unrelated bases is not claimed here.

This solves a nonlinear recursive PUSH family that the previous debt-only
cutoff theorem cannot supply. It does not prove that arbitrary recursive
mixtures of additions, copying and cancellation retain automatic value sets.

## 5. Conditional undecidability of added zero-test guards

The full left pair can encode two counters as `E(c1,c2)=(c1,c2,0)`. Direct
calculations give the following transitions:

| Counter operation | Exact context | Guard needed for the decrement |
| --- | --- | --- |
| increment c1 | `replay(L_1,W)` | none |
| increment c2 | `replay(W,P_1)` | none |
| decrement c1 | `prefix(0,1,W)` | c1>0 |
| decrement c2 | `replay(W,L_1)` | c2>0 |

At zero the decrement contexts modify the other coordinate, rather than block:
`prefix(0,1,(0,n,0))=(0,n+1,0)` and
`replay((p,0,0),L_1)=(p+1,0,0)`. This is exactly why guards cannot be omitted.

If a strengthened grammar permits productions enabled by `p=0`, `p>0`, `n=0`
or `n>0` at the selected child, create one nonterminal per counter-machine
control state and encode increment transitions by the first two contexts. Encode
each zero/decrement instruction by an identity edge under its zero guard and
a decrement edge under its positive guard. Seed the initial state with its
encoded initial counter pair. Induction on derivations and machine runs gives
exact equality of the encoded reachable configurations. All productions are
linear, each with one child; copying, swap, both and right debt are unnecessary.

The CM2 instruction set in Dudenhefner's **Certified Decision Procedures for
Two-Counter Machines**, FSCD 2022, Definition 2 and Theorem 6, has undecidable
halting. Its successful-decrement conditional jump is explicit, avoiding an
incorrect transfer between different two-counter instruction sets. Appending
a distinct target state to halting positions transfers that result to control
reachability of the guarded grammar above. Primary source:
[paper, pp. 16:3–16:4](https://drops.dagstuhl.de/storage/00lipics/lipics-vol228-fscd2022/LIPIcs.FSCD.2022.16/LIPIcs.FSCD.2022.16.pdf).

**This is not the source model.** Ordinary local observations do not license
production enabling. The assigned grammar has no guards; global Simple-sub
failure is not pruning an invalid derivation and all structural children
propagate. No source guard correspondence was established here. Consequently
this reduction proves neither undecidability nor a production restriction for
the actual source problem.

## 6. Why the obvious one-PVAS bridge is incomplete

With right debt absent, independent-child replay, constants and raw left
prefixes flatten to a context-free word grammar in PUSH/POP; this flattening is
valid in that subalgebra only. The resulting word has reduced pair `(p,n)`.
Starting a nonnegative counter at `a`, it is executable exactly when `a>=p`,
and then ends at `n+a-p`. Hence its reachability relation is

```
{(a,n+a-p) | (p,n) is a generated pair, a>=p}.
```

That is a one-dimensional grammar vector addition system relation. Bizière and
Czerwiński's **Reachability in One-Dimensional Pushdown Vector Addition Systems
is Decidable** supplies a real decidability result for that relation, rather
than the older coverability-only result. The primary author preprint was
retrieved at [arXiv:2411.02386](https://arxiv.org/abs/2411.02386); this lane
relies only on its stated main theorem and does not claim to implement or audit
its thin-GVAS transformation.

The relation forgets dominated pairs. A grammar supplying just identity and
a grammar supplying identity plus `(1,1,0)` have the identical counter
reachability relation `{(a,a) | a>=0}`. Their active-count, leading-debt and
per-node observations differ. Therefore merely citing one-PVAS decidability
does not solve the requested full-pair observation problem. It does decide
some predicates, for example whether a generated pair is exactly `(0,k)` by
querying reachability from 0 to k, but that does not recover the complete set.
Raw right debt, nonassociative mix and correlated child copying also require
additional translations. None is silently supplied by this citation.

## 7. Verification, frozen inputs, and handoff

The sole scratch checker is
`/workspace/scratch/15155572c47b/recursive_push_attack/check.py`. It imports the
assigned count operations and compares accelerated formulas with exact repeated
application. At raw prefix/replay nodes it also uses the supplied independent
literal-token evaluator. Both evaluators share the frozen operation premises;
these are bounded implementation-consistency checks, not independent source
semantics or a proof of the general algorithm.

Two sequential Python processes ran successfully, within a 30 s timeout and
256 MiB address-space limit each:

```
timeout 30s bash -c 'ulimit -v 262144; exec python3 -B /workspace/scratch/15155572c47b/recursive_push_attack/check.py --pilot'
timeout 30s bash -c 'ulimit -v 262144; exec python3 -B /workspace/scratch/15155572c47b/recursive_push_attack/check.py'
```

Pilot: PASS, 4,320 orbit comparisons and 8,640 raw token checks; 864 full-pair
growth checks; 240 full-pair doubling checks; 100 guarded-update cases; 8,192
finite-automaton checks. User CPU 0.110139 s, system CPU 0.014239 s, internally
measured wall 0.065819 s, maximum RSS 11,988 KiB.

Full run: PASS, 115,200 orbit comparisons and 230,400 raw token checks;
23,040 full-pair growth checks; 240 full-pair doubling checks; 100 guarded-update
cases; 8,192 finite-automaton checks. User CPU 1.685771 s, system CPU 0.012494 s,
internally measured wall 1.636688 s, maximum RSS 11,992 KiB. Acceleration seeds
have `p,n=0..7,r=0..2`, `a=1..4,b=0..4`, and comparisons at depths 0..29.
Doubling covers `h=1..4,x=0..4,k=0..11`. Automaton checks exhaust addition
triples in 0..15 and `Pow2` inputs 0..4095. The finite automata closure algorithm
for entire observers is proved constructively above; it was not implemented by
this checker. No cutoff witness is counted as the new result.

No random seed, omitted shard, timeout, killed process or failed Python run.
No Cargo, production test, build, formatter, Git operation, child agent or
source-pipeline archaeology. The two successful processes consume about
1.796 user CPU seconds in total; no third process is required.

Frozen direct dependency SHA-256 snapshot:

```
ab9a26a0d1115a18e563b0119b919632b385407bea5107d1cecefaed9b07e46e AGENTS.md
5788a2ef1c2181b43a9f82116fe6c4cfd32419dc7098fb84fa7c0d46a0a88ca6 rules/research-lab.md
4477be1344edb73e2873f94233d760c9a600bee6adbaaff3ec812a49c5219e7b rules/design-authority.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e rules/git-concurrency.md
6edc09e9481e8cfd5d9d5a455d08210f5a99fab4f98b359c0cdc9beca9586c63 mixed-replay-observer-construction
be959f1b33298687075ec197f606a09d3c3955dc498abb58ef7c3e63e69cf903 mixed-replay-algebra-attack
33b332d25c68d9ab10620d4c5d94d367602617a816f3172f1ce716b58ad9b3dc bracketed-replay-decision-obstructions
c6f3d36462469494dcdaa5fd6e22029bcea0f5d48a258e5eb55bc41a65dfaf6c tools/research_mixed_debt_observer.py
```

Dependencies were not modified by this lane. The primary must recheck these
hashes against its integration snapshot. Final claims remain producer work
awaiting independent review. No source grammar was certified, no language
semantics changed, and no production gate closed.

Commit packet: only `notes/progress/2026-10-10-recursive-push-algebra-attack.md`;
baseline and Oracle above; unreviewed research-only conditional derivations and
bounded consistency evidence. Scratch checker is supporting evidence, not a
repository commit candidate. Suggested subject:
`research: accelerate full-pair recursive PUSH subcases`.
Shared task/theory/index edits are intentionally deferred to the primary.

Recommended next action: independently review sections 1–4, then test whether
the actual source cycles have these forms or a richer exact arithmetic
decomposition. Preserve the general unguarded recursive PUSH gate as open.
The guarded-machine reduction and a one-PVAS citation must not be substituted
for that missing correspondence or general observation proof.
