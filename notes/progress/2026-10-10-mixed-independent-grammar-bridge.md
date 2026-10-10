# Actual mixed replay grammar and the exact BVAS translation seam

Date: 2026-10-10
Status: producer-frozen, unreviewed research characterization and failed reduction; no decision theorem, source closure or production authority
Successor code baseline: `f75c8d2fc27c8e5f61e13632b234d56314d2a62c`
Pinned Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive persistent lease: this note
Scratch: `/workspace/scratch/15155572c47b/mixed_independent_bridge/`

## 1. Result

The primitive full-context propagation/replay interface is **unary context
transport plus independent binary bound replay**, with an atomic unary copy
`both(p,n,r)=(r,0,r)`. A Function firing emits several unary images of the
same incoming record. It does not install a shared-child binder into later
bound replay. Lower and upper collections retain independent records; replay
compares their Cartesian product. SCC endpoint equality changes their owner
and unions collections, without correlating the selected lower and upper.

This distinction invalidates application of the shared-child PCP theorem to
the primitive interface. It also invalidates replacing atomic `both` by a
binary rule with independent children. The latter replacement adds a false
identity witness in the four-unit example proved in section 5.

The July 2026 BVAS reachability preprint has been checked directly. Its
transitions add a fixed vector to the sum of child vectors. That result does
not immediately decide our grammar: exact recursive mix requires maximal
cancellation at each node, and atomic `both` duplicates the exact same
unbounded right vector. Sections 5–7 identify the concrete compositional
translation missing from a BVAS/PVASS route, rather than assuming that a
piecewise Presburger operation is a BVAS transition.

No impossibility or decidability conclusion for the complete mixed primitive
grammar follows. No count/depth cap, PUSH exclusion, new enabling condition,
source restriction or semantic change is proposed. The remaining mathematical
step is an exact finite counter-system realization of the actual node
interfaces, closed under unbounded recursive composition, with no intermediate
zero tests. Full production additionally has count-parameterized residual
endpoint generation; it is not already a proved finite nonterminal grammar.

## 2. Exact numeric operators and retained decorations

Fix the attachment IDs actually present in a supplied primitive descriptor.
For each ID i retain `(p_i,n_i,r_i)` in `N^3`: leading left POPs, active left
PUSHes, and right POPs. This is the natural-count lift. Oracle stores u32
counts: POP additions saturate in the inspected owners, while active PUSH
addition uses ordinary u32 arithmetic. The natural equations agree with its
nonoverflowing count operations; overflow behavior is not a finiteness proof.
Counts do not identify authentic IDs, family decorations, filters, endpoints
or authority references.

For left composition and subsequent replay put

```
p0_i = p1_i + max(p2_i-n1_i,0)
n0_i = n2_i + max(n1_i-p2_i,0)
r0_i = r1_i+r2_i.
```

The count projection of actual directed mix is exactly

```
if r0_i=0:          (p0_i,n0_i,0)
else if n0_i>r0_i:  (p0_i,n0_i-r0_i,0)
else:              (0,0,p0_i+r0_i-n0_i).
```

This per-ID numeric formula respects the actual global empty-side shortcut.
If left is globally empty, p0_i=n0_i=0 and the last case gives the original
right count. If right is globally empty, every first case applies. In the
remaining case the actual loop visits each positive-right ID, appends its POPs,
keeps an active result left, or moves a pure debt right. IDs with no right
entry keep their left pair. This is `directed_weight.rs:16–39,137–176`.

The other primitive count maps are

```
swap_i(p,n,r)=(r,0,p)
both_i(p,n,r)=(r,0,r)
prefix_(a,b),i(p,n,r)=(a+max(p-b,0), n+max(b-p,0), r)
suffix_c,i(p,n,r)=(p,n,r+c).
```

These are `constraints/mod.rs:3566–3612`. Swap and both act globally on all
IDs, rather than permitting a selected-ID copy. They reset the left filter to
All by `LeftConstraintWeight::from_right_weight` at
`directed_weight.rs:243–248`. Prefix and replay intersect left filters; suffix
preserves the existing left filter. Mix changes directed counts while
preserving that filter (`constraints/mod.rs:3624–3638`). Active families and
their compatibility must also remain in the descriptor; the numeric formula
alone is not a theorem about family merge or nominal arguments.

Prefix, suffix, swap and both have **raw** results. There is no automatic
normalization after every unary map. Replay normalizes at its written binary
node; Var–Var canonicalization also normalizes
(`machine/entry.rs:1092–1117`). A raw both result can therefore carry equal
left and right debts simultaneously. Mixing it early changes the primitive
expression and cannot be assumed.

## 3. Grammar of primitive closure, including all four Function ports

For a fixed endpoint/owner presentation use nonterminals

```
C_(a,b): contexts on positive a <: negative b
L_(v,a): contexts on a retained lower a of owner v
U_(v,b): contexts on a retained upper b of owner v.
```

Their denotations are sets of exact whole context records, including
decorations. A base submission supplies a finite constant to C. Wrapper
normalization supplies the unary rules

```
C_(inner,b) <- prefix_W(C_(Stack(inner,W),b))
C_(inner,b) <- prefix_W(C_(NonSubtract(inner,W),b))
C_(a,inner) <- suffix_W(C_(a,NegStack(inner,W))).
```

The last rule consumes/checks the upper wrapper's filter at the actual owner
before forwarding its POP projection (`propagate.rs:9–57`). Union branches,
Intersection branches and ordinary covariant structural children transport
one selected incoming context unchanged; contravariant children transport its
swap. Tuple, Record, Variant and invariant nominal argument rules use the
corresponding fixed child endpoints (`propagate.rs:58–105,275–333,413ff`).
These are unary rules for each child, even when several child rules have one
parent. Diagnostic/proof provenance can remember that firing, but the later
set-valued replay does not require the children to select that firing again.

For a positive Function A and a negative Function D, the actual rules are:

| Child | Endpoints | Context map |
| --- | --- | --- |
| Value argument | `D.arg <: A.arg` | `swap` |
| Argument Effect, ordinary branch | `D.arg_eff <: A.arg_eff` | `swap` |
| Argument Effect, pure passthrough branch | `D.arg_eff <: strip_stacks(D.ret_eff)` | raw `both` |
| Return Effect | `A.ret_eff <: D.ret_eff` | identity |
| Return Value | `A.ret <: D.ret` | identity |

The branch test is exactly the syntactic `A.arg_eff=Neg::Bot`, not an
observation that some current or future bound is pure
(`propagate.rs:207–271`). `strip_stacks` walks negative Stack wrappers
(`:401–410`); it is not a replay or independent choice. There are four ports;
the two argument-Effect rows in the table are alternative rules for one port.
No rule binds t and computes `replay(t,projection(t))` as one shared expression.
In particular the reviewed callback source has a negative empty Row rather
than Neg::Bot and selects the ordinary argument-Effect rule.

For insertion, the basic retained-bound rules are

```
L_(v,a) <- erase_filter(C_(a,Var(v)))
U_(v,b) <- erase_filter(C_(Var(v),b)).
```

They include the insertion-time checks and extrusion's endpoint mapping at
their actual location; they do not simply erase a check as an algebraic
identity. A Var–Var edge may install records on both sides. The primitive
binary rule at pivot v is

```
C_(a,b) <- Replay(L_(v,a), U_(v,b)).
```

Every retained lower/upper pair is eligible, including pairs whose proof
trees happen to share an ancestor. The two occurrences choose independently
from their collections. A repeated nonterminal on the two sides is still
an independent choice. `bounds.rs:3388–3472` snapshots all upper records when
a new lower arrives; `:3560–3648` snapshots all lowers for a new upper, and
uses `lower.weights.compose_for_replay(upper.weights)` in that order. Both
arrival directions therefore present the same Cartesian closure, with exact
mixed bracketing at each binary replay.

Oracle admission then applies its actual canonicalization, exact duplicate,
terminal erasure, equal Var–Var omission, Var-only support-cycle subsumption,
and proof-route/evidence policies (`entry.rs:1092–1117,1783–1816`;
`bounds.rs:3650–3713,4274–4318`). Those are operational Oracle restrictions,
not premises proving arbitrary selected Simple-sub contexts harmless. This
note distinguishes the numeric primitive closure from the admission layer.
It does not claim that all unpruned grammar derivations are stored by Oracle,
or adopt its omission policies as the successor's semantic contract.

## 4. Future lowers, SCC equality and residual endpoint production

An upper insertion with non-All left filter f checks the current stack and
registers `(v,f)` for existing and future positive lowers before storing the
filter-erased context (`bounds.rs:3193–3255`). Let F_v denote that registration
set. The additional obligation is a Cartesian pairing of every f in F_v with
every retained L_(v,a), checked with that lower's exact context. A new
registration visits current lowers; a new lower visits current registrations
(`:3272–3301`, and `add_lower_bound` at `:630–739`). Thus it is not sufficient
to observe only the original upper context after erasure.

The weighted check first tests the active left stack against the supplied f,
then checks the concrete positive type under the intersection of f and its
retained filter. Traversing Pos::Var
can register another future-lower filter; Function ports are not recursively
visited by this concrete-head check (`:3305–3360`). These checks are obligations
of generated records, not new guards choosing which finite weight derivation
exists. Existence of an entirely passing solver run must not be confused with
existence of one weight passing a final observation.

For SCC parent/copy equality, write rho for the new representative map. The
contextual lifting required by this primitive interface transports each
retained record separately,

```
L_(v,a,w) -> L_(rho(v),rho(a),w)
U_(v,b,w) -> U_(rho(v),rho(b),w),
```

with authentic attachment/authority remapping where the actual transport
owner requires it. It unions collections and registrations, then replays
new cross pairs. It does not select one w for both sides. Current successor
`candidate_intrusion.rs:493–604` appends both bound sides, updates the
representative/generation, and replays lowers; it has no context field at this
baseline. This equation is therefore the required contextual extension of
the existing collection rule, not a claim that it is already implemented.
The new owner-gate note records the same Cartesian distinction.

An upper-only self record U_(v,v,w) consequently allows
`Replay(L_(v,a),U_(v,v))` to produce a further lower at v. Endpoint equality
does not make w identity. Oracle's equal Var–Var omission is a separate
inspected admission fact, not a proof that this mixed self rule can be deleted.

The complete production grammar is not already finite merely because source
syntax is finite. `constraints/row_effect.rs:120–234` checks/erases a row
filter, retains concrete heads admitted by the current active stack, subtracts
their families while preserving counts, and uses the exact residual key

```
(source, sorted retained families, residual LEFT weight)
```

to allocate/reuse gamma. It emits an unweighted source-to-retained-row task
and a weighted gamma-to-original-tail task. The latter retains the original
right weight and normalizes the directed mix at that written point. Right
weight and tail are not in gamma's cache key. Future gamma bounds use the
same independent binary replay. `:1190–1244` preserves per-ID POP/PUSH counts
while changing their active family and can emit invariant payload tasks.

Thus a precise full presentation includes parameterized endpoint constructors
and family/payload tasks in addition to the fixed-endpoint weight grammar.
There is no demonstrated finite residual template quotient here. Assuming
one would be a new unproved premise. The decision attempt below already
stops at the smaller, exactly specified numeric primitive interface, so this
additional owner-generation issue is not used to excuse its missing proof.

## 5. Atomic both remains correlated: an exact counterexample

For one authentic ID put I=(0,0,0), P_k=(0,k,0), R_k=(0,0,k). Let T have
exactly the independent alternatives R_1 and R_3. The actual unary expression

```
B = Replay(I,both(T))
```

has exactly `{R_2,R_6}`. Each both firing selects one T value, duplicates its
right count atomically, and the written replay mixes the two debts. However
an independent binary replacement `Replay(T,T)` has `{R_2,R_4,R_6}` because
it can select R_1 and R_3 separately. Therefore

```
Replay(P_4,B)                  never has identity
Replay(P_4,Replay(T,T))        can have identity.
```

For the actual B alternatives the outer results are P_2 and R_2. The false
replacement has an extra I result. This is a false exact-support witness using
only constants, independent binary replay, and the one actual atomic copy.
It does not require arbitrary shared term DAGs or multiple IDs. It proves
that independent-child BVAS merging cannot replace that unary primitive.
It does not by itself prove that this support query is an independently
required production observer or that every such grammar is source-generated.

## 6. Maximal cancellation cannot be weakened at recursive interfaces

A second common translation proposal implements cancellation by repeatedly
decrementing two nonnegative counters together, then exits nondeterministically.
It recognizes partial cancellation as well as the actual maximal result unless
the exit proves that an appropriate residual counter is zero.

That missing local requirement is observable under actual later operations:

```
t_actual = Replay(P_2,R_1) = P_1
t_bad    = raw (0,2,1)        // cancellation loop exits before one step
C(t)     = Replay(P_1,swap(t)).

C(t_actual)=P_1
C(t_bad)=I.
```

This is another false identity witness. Keeping the raw unconsumed right
counter for later normalization does not repair it: swap is allowed at the
next primitive node and discards the active left part before that normalization.
Conversely, forcing normalization after every unary operation would change
the actual raw-both and raw-prefix interfaces.

In the left-only PVASS theorem, one global-minimum marker per finitely many
observer inputs carries a frozen counter required to be zero at the **final**
point target. A recursively mixed grammar has unboundedly many internal nodes
at which this exact interface must be established before further swap/both
and binary replay. Reusing a scratch counter without proving each local zero
boundary can allow an ancestor to consume an earlier node's leftover. Reserving
one frozen counter per node would not be a finite-dimensional reduction.
These observations reject that attempted construction; they do not establish
that every other encoding fails.

## 7. Primary counter-system results and the concrete missing lemma

Bizière, Leroux and Sutre, **Solving the Reachability Problem for Branching
Vector Addition Systems via Semilinear Inductive Invariants**, submitted
10 July 2026, [arXiv:2607.09558](https://arxiv.org/abs/2607.09558), was inspected
in its [primary full paper](https://arxiv.org/pdf/2607.09558), sections 1–2.
It states decidability of BVAS point reachability by separating unreachable
configurations using semilinear inductive invariants. Its model forms an
internal configuration by summing its independent child vectors and adding
a fixed action vector, with nonnegativity. It does not state a reachability
theorem for arbitrary piecewise-affine Presburger node relations, nor for
same-child copying or intermediate exact-zero interfaces. This is a verified
preprint claim, not a new reviewed premise of a mixed-grammar theorem here.

Blondin and Raskin, **The Complexity of Reachability in Affine Vector Addition
Systems with States**, LMCS 17(3:3), 2021,
[DOI 10.46298/LMCS-17(3:3)2021](https://doi.org/10.46298/LMCS-17(3:3)2021),
[primary paper](https://arxiv.org/pdf/1909.02579), sections 2 and 4, classifies
reachability for classes of affine updates. Its matrix-class definition closes
under counter-subset renaming and identity extensions; standard reachability
also requires each affine result to remain nonnegative. The actual global
swap/both operations are not a demonstrated realization of arbitrary selective
counter updates, and our saturation is total rather than a failing decrement.
Its class-level undecidability result therefore does not give a reduction to
the authentic grammar. No Minsky zero-test guard is imported.

The precise outstanding translation lemma is:

> Given a finite grammar with constants, raw global swap/both, raw fixed
> prefixes/right suffixes and independently selected binary **actual** replay,
> construct a finite-dimensional BVAS or PVASS whose point reachability is
> equivalent to an exact prescribed root observation, while ensuring every
> recursively reusable node exports its exact raw/normalized interface.
> The construction must enforce atomic duplication and maximal cancellation
> at unboundedly many internal nodes without adding a zero-test transition,
> correlating independent binary children, or allocating one dimension per
> derivation node.

This is a concrete interface obligation, not the statement that finite grammar
existence or Presburger-definability decides closure. Each individual operation
has a Presburger graph; composing finitely many such graphs in an observer is
effective. Recursive closure under those graphs is the unsettled step. Both
minimal witnesses above falsify proposed relaxations of exactly that step.

An alternate undecidability route must construct its simulation using these
same raw unary and independent binary operations. The shared-child PCP affine
maps reuse a selected recursive t in t, A(t), and B(t), and do not supply such
a simulation. Ordinary production storage supplies independent bound choices,
not that binder. Neither direction is completed in this note.

## 8. Checks, frozen dependencies and handoff

One Python process ran under 30 s / 256 MiB:

```
timeout 30s bash -c 'ulimit -v 262144; time python3 -B /workspace/scratch/15155572c47b/mixed_independent_bridge/check.py'
```

It passed the explicit atomic-copy and premature-mix false-identity witnesses,
and the established mixed-bracketing discriminator. Wall 0.023 s, user 0.017 s,
system 0.005 s; RSS was not measured. An earlier launch requested unavailable
`/usr/bin/time` and exited 127 before Python started; it is not a successful
check or a second Python process. No timeout, omitted case shard, Cargo,
Oracle execution, compiler build/test, broad suite, child agent or Git mutation.
The check transcribes inspected equations and is not independent source or
mathematical review.

Read-only pinned Git blob reads supplied the Oracle source. Successor SCC
source and the two live owner/cycle notes were read narrowly; their conclusions
were not promoted to source grammar completeness. Direct hashes at freeze:

```
69dfc39c031f7dc72808163c743135bd4f69153501e04439b9d341f3fa53a07b  recursive-push-observer-construction
931ada059da5fc6aa89ab5a4e63330c14b490cb853ff3b959984ad32ad220e0b  complete-mixed-effect-construction
22e9998c0e0b9d4a6a32dbe07777586c7109b8f643481ddf02bc2a22abff8a2d  contextual-residual-owner-gate
6e39179625abb47cf6fc7cb3eb6338ea53b83033c8d046f128c697463a483aca  mixed-replay-source-cycle
c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7  Oracle machine/bounds.rs
de71ae7ed5a5aed22f3e5d35ca0ebcd52872ff965fcc22523a662cffdd6f28db  Oracle directed_weight.rs
00c70ca0938b24d4d2dd38de6598fe54217aebd28150ac279b52839046b340b8  Oracle machine/entry.rs
ad3cf5fd60462cb1a08ef1a5d6fc57c4fd640148597bc3b331d09729616d8392  Oracle constraints/mod.rs
8695fa5d7dfac805cd7d66e9e0760c8c298002b952b0cd8a43dcd1f8eb6f7086  Oracle machine/propagate.rs
080472bb5dcb3f724e808ff745c6fba304cc7ea2574b8f8eb3e3466964e937c2  Oracle row_effect.rs
```

Persistent changed path: this note only. Scratch source copies and checker
are outside the commit lease. Frozen claim class: unreviewed source-rule
characterization, two proved algebraic falsifiers, and a narrowed incomplete
decision reduction. Suggested subject: `research: pin independent mixed replay grammar and BVAS seam`.
Primary owns Git integration and shared task/theory/index updates. Suggested
record delta: distinguish independent binary replay with atomic both from
arbitrary recursive shared-child grammars; keep exact compositional counter
translation, finite residual representation and actual required observation
bridge open. Do not declare complete mixed Effect, hygiene, source inference,
soundness, principality or cutover closed.
