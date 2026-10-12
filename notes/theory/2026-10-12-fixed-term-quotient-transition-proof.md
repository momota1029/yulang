# Fixed recursive core: a finite quotient transition at extrusion return

Date: 2026-10-12
Status: independently reviewed provisional mathematical construction and
bounded derivation; no adopted transport/scheduling contract, compiler
correspondence or parent-gate closure
Baseline supplied by primary: `5e7ffb735fc1a829d03890ebfd353e17ad7ca342`
Branch supplied by primary: `research/simple-sub-intrusion`
Exclusive lease: this file only; prover leaf, no delegation

## 1. Frozen claim, domain, binders and exclusions

Fix exactly:

```text
let rec odd = lambda n_outer.
  let rec even = lambda n_inner. odd n_inner
  in even n_outer
in odd
```

O/E are distinct source definition Values; a/b are distinct formal Values;
the inner/outer Apply results are two further distinct Values. Solver rows
o/e/A/B/R/C/D below are a different domain. O is monomorphic throughout its
initializer, E throughout its own initializer. E publication remains boundary
1 and O publication boundary 0. Both Lambda binders retain their original
lexical scopes. No definition roots, source Values or scopes are equated.

The event is the actual negative demand extrusion from the inner call. Its
origin is E, receiver O, and retained polar pairs are exactly `(C,B,+,1)` and
`(D,R,-,1)`. The approved source graph contains O -> E and E -> O. Both pairs
qualify jointly. The in-process raw cache contains `(o,F(B,R))`; the returned
raw extrusion demand is `F(C,D)`. F denotes Function. These identities, the
polar memo and parent provenance are frozen, rather than replaced by quotient
cache keys.

The finite mathematical claim is the following, quantified up to any injective
renaming of allocated identities. Start at level 0 with the exact native
prefix for this term, stop after both ordinary extrusion copies/direct links
have been constructed and the extrusion has returned F(C,D), but before
`constrain` recursively processes that returned demand. Represent its live
store and suspended constructor values explicitly as in section 3. The
explicitly defined finite transition Q in section 4:

1. forms exactly the equality classes B=C and R=D;
2. gives a lawful leveled active store, unchanged raw pending cache and
   provenance, and the precisely enumerated rewritten continuation;
3. permits the original returned-demand comparison and every remaining native
   App, recursive completion, replay, generalization and fresh use;
4. yields the cut store of the frozen input's section 5, and its final native
   simplified interface Theta = Top -> Bot.

The proof also reproduces the fixed source typing of Theta and its order
below every finite paper Fig.3 typing of this term. No H is a premise. Q is a
defined operation on an enumerated finite state, and its consequences are
calculated below. Its definition is **provisional mathematical work**, not
evidence that an existing source owner emits Q, or that the approved equality
decision uniquely entails this representation and timing.

The original parent claim keeps its full supported-source/use-history
quantifiers, complete Call meaning, effects, attachment/provider/witness and
residual lineage, source soundness, required principality and normal progress.
This result does not discharge that claim. Arbitrary future uses, different
terms, general representative/level policies, early graph production, Yulang
admission, effect transport, abnormal paths, all-assignment preservation,
runtime semantics and F5 cutover are excluded from this bounded derivation.
The pure reference term contains no effect or complete Yulang Call objects;
their absence supplies no proof of their contracts.

Falsifiers are a missing live slot in section 3, a native source rule emitting
a different suffix comparison, an incorrectly skipped returned demand, a
violated bound-level invariant, or a final compact interface differing from
Theta. An actual constructor's inability to realize Q refutes a proposed
implementation bridge, rather than this finite state calculation.

## 2. Authority, dependencies and actual owners

Governing sections are top-level inference principles sections 1–5;
parent-copy SCC design **Selected operation and compiler responsibility**,
**Nested Apply membership**, **Definition-root Value ownership** and
**Retained boundary**; value/type association **Approved extrusion-event
qualification**, **Definition-root origin for nested call-demand extrusion**
and **Implementation and proof boundary**; copied-row ownership **Decision**
and **Scope and proof boundary**. These select the qualified equalities and
preserve source ownership. They leave the general scheduling/transport scheme
unselected. This note selects none for production.

Frozen direct research input:
`notes/theory/2026-10-12-fixed-term-intrusion-quotient-proof.md`, especially
sections 1–6. Its independent review applies to its conditional result, not
to this new construction. The fixed source argument is also in
`notes/theory/2026-10-12-cross-level-recursive-scc-core-proof.md`, section 5.

Reference root: `/home/momota1029/rust/simple-sub-reference`.

| Responsibility | Actual owner, shared/src/main/scala/simplesub |
| --- | --- |
| Recursive root, completion and scheme boundary | `Typer.scala:48–55` |
| Name, Lambda, App and nested Let | `Typer.scala:59–83` |
| Raw identity test/cache before comparison | `Typer.scala:88–103` |
| Function variance, bound insertion and opposite replay | `Typer.scala:106–126` |
| Polar copies, memo and direct links | `Typer.scala:134–156` |
| Per-use unsigned memo and level cutoff | `Typer.scala:166–188,199–207` |
| Structural level and immutable allocation level | `Typer.scala:209–227` |
| Canonical variable closure | `TypeSimplifier.scala:102–157` |
| Removal of variables occurring at one polarity | `TypeSimplifier.scala:185–239` |
| Empty positive/negative compact coalescing | `TypeSimplifier.scala:286–319` |

The Scala source has immutable Lambda/App local values and no equality-state
transition, source Value graph or occurrence-certificate consumer. Explicit
frames below expose the values those actual constructors suspend; they are
a mathematical evaluation representation, not a claim that Scala exposes
rewritable frame objects. The prefix/suffix native steps correspond to the
listed bodies; Q itself has no corresponding body in the inspected reference.

## 3. Exact cut state and inventory of live consumers

Ordinary recursive allocation introduces o,A at level 1 and e,B,R at level 2.
The first App compares o below F(B,R). Its cache records the raw pair before
negative extrusion. The two variable cases create C,D at level 1, record
`M(B,+)=C`, `M(R,-)=D`, and install U(B)=[C], L(R)=[D]. Both copied opposite
lists are empty. Stop after the Function extrusion returns F(C,D), before
the `constrain` call at line 123. The active native store is:

```text
o,A,C,D : level 1        e,B,R : level 2
U(B)=[C]                L(R)=[D]
every other list empty
K={(o,F(B,R))}          returned demand = F(C,D)
```

The current native judgment is suspended at `constrain`'s extrusion-return
seam, not at the generation of an already completed comparison. The recursive
call on F(C,D) is still owed.

For this fixed evaluation, the complete live continuation inventory is:

| Constructor/context slot | Value at the cut | Next actual use |
| --- | --- | --- |
| Extrusion-return comparison | lhs o; returned rhs F(C,D); existing K | Compare the returned demand under the same cache |
| Inner App | callee o, argument B, forced lazy result R | Return its result R after comparison |
| Inner Lambda | parameter B; awaiting the App result | Construct F(B, returned result) |
| Inner recursive RHS | recursive root e; awaiting that Lambda | Compare returned Lambda below e, then publish e at 1 |
| Outer Let continuation | outer context; awaiting E's scheme | Extend that context by E, infer `even n_outer` |
| Outer Lambda | parameter A; awaiting Let body | Construct F(A, returned result) |
| Outer recursive RHS | root o; awaiting outer Lambda | Compare returned Lambda below o, publish o at 0 |
| Outer Let/final Name | outer level-0 context; awaiting O's scheme | Instantiate the final O Name |

The relevant nested contexts are maps from original resolved binders to
schemes. They contain O:o, outer formal a:A, and, within E, E:e and formal
b:B. Their binder keys and context level numbers are retained. Every context
copy stored by these frames is included, including the inner App context even
though it has no subsequent Name lookup. Builtin/external entries, if present,
contain none of B/R and are unchanged. No second result or provider slot exists
in this four-constructor reference syntax.

The pending caller also holds the old rhs0 F(B,R) whose extrusion has now
completed. Inspection of lines 121–123 shows that rhs0 has no further semantic
read: the next call uses the returned rhs. Its raw identity is retained for
the existing cache key. The completed extrusion's polar memo and pair record
likewise retain their original identities; no further extrusion recursion or
memo lookup remains at this cut. This liveness statement is confined to the
exact source body and this exact returned Function.

The state representation has three distinct domains:

* The allocation/provenance ledger retains every raw ID, original allocation
  level, event ID, pair polarity/target and origin/receiver.
* The active store assigns bound lists and semantic levels to current class
  representatives. Before Q each raw allocated row is its own representative.
* Live type-valued slots are contexts, constructor frame values, store payloads
  and the returned demand. Historical raw cache/provenance records are outside
  that set. They are not type operands awaiting evaluation.

There is one authority for active bounds. Historical parent rows are not a
second store from which a later generalizer may recover old bound lists.

## 4. Defined finite transition Q

Define q(B)=C, q(R)=D, and q identity on all other raw IDs. Write X=C and
Y=D for the existing low anchors; these are aliases in notation, not new
allocations. On live type descriptions define:

```text
q(v) = the specified representative of v
q(F(l,r)) = a Function description with children q(l),q(r)
q(PolymorphicType(k,t)) = PolymorphicType(k,q(t))
```

No structural node's cached level is transported from an old description.
Each rebuilt live Function derives its level from its actual children,
exactly as the native Function constructor does. Here the only old high
Function is historical F(B,R); the returned F(C,D) is already low and needs
no change. Later Lambda descriptions are constructed from rewritten slots.

Q is the following finite state operation, performed once on the cut domain:

1. Keep the allocation/provenance ledger, resolved source tree, graph and
   occurrence record byte-for-byte in their respective identity domains.
   Keep K and M unchanged as raw maps/sets. Preserve the returned raw demand
   F(C,D).
2. Replace the two singleton class pairs by {B,C} represented by C, and {R,D}
   represented by D. Keep all other classes singleton. The representative
   levels are the **existing** C/D allocation levels, both 1. No raw allocation
   level is mutated; no new row or unrelated equality is introduced.
3. For each resulting class, concatenate the pre-cut lower lists of its
   members and separately concatenate the upper lists, mapping every payload
   by q. For this exact store the only resulting nonempty lists are U(C)=[C]
   and L(D)=[D]. There is no list-order ambiguity or lost multiplicity: each
   merged side has at most one element.
4. Map every live type-valued context/frame slot by q, preserving constructor
   tags, syntax, binder keys, source locations, scope numbers and control
   position. The inner App's already forced result slot becomes D, its
   argument becomes C, and the inner Lambda's parameter slot becomes C.
   o/e/A, all recursive-root slots and all publication limits are unchanged.
5. Account for newly combined lower/upper products before resumption. For C
   the lower list is empty; for D the upper list is empty. The other rows
   are unchanged and have no bounds at this cut. Every product is empty.
   Thus there is no additional comparison to enqueue or silently omit here.
   Resume the owed native comparison `constrain(o,F(C,D))` using unchanged K.

Items 1–4 define Q explicitly. They do not assume that some unspecified H
performs them. Item 5 calculates the propagation obligation at this particular
union, including third-owner rows o/e/A. It is not a universal equality-replay
algorithm: there is no row j with two newly interacting structural bounds in
this pre-store.

All future semantic consumers in the specified suffix use the resulting
concrete representative operands and store. Native insertion and replay read
these representative lists; Lambda/App read their mapped slots; publication
uses the original limit and mapped body; freshening and simplification traverse
the active lists. No later blanket rewrite or custom native comparison rule
is needed: none of those operands contains B/R after this finite transform.
The only B/R occurrences left are dormant raw cache/memo/provenance entries.
No general fresh-use memo exists yet at the cut and none is merged with M.

This is a finite construction: two class mergers, two nonempty stored link
payloads and the finite frame/context inventory above. It requires no search
over typings or solver assignments, no constraint solved at generation, no
retargeted Value incidence and no downward dependency closure. No general
time/space bound or production storage optimization follows from its finite
size.

## 5. Cut postcondition and native returned-demand insertion

After Q, before resuming the comparison:

```text
active level 1: o,A,X,Y        active level 2: e
U(X)=[X]                      L(Y)=[Y]
all other lists empty
K={(o,F(B,R))}                returned raw demand F(C,D)
```

The only bound payloads have level 1, equal to their owner levels. q is
idempotent and the live payloads/slots are already fixed by q. Binder b remains
the same lexically local formal with its original context at level 2; its
monomorphic assigned coordinate is now X. The App result Value also remains
its original distinct Value with assigned coordinate Y. Reducing a coordinate's
live representation does not merge source binders or move their declarations.
No statement that arbitrary generalized source interfaces are preserved is
inferred from this observation.

Because Variable equality is raw object identity and Function equality compares
raw children, F(B,R) and F(C,D) remain distinct cache operands even though the
active equality classes have merged. Thus the native cache check does not find
`(o,F(C,D))`; it inserts that second raw pair. Its level guard reads the actual
returned Function's level 1, so line 116 inserts U(o)=[F(X,Y)]. L(o) is empty,
hence no replay is generated. This proves precisely the frozen input's section
5 initial store:

```text
level 1: o,A,X,Y; level 2: e
U(o)=[F(X,Y)]    U(X)=[X]    L(Y)=[Y]
all other lists empty.
```

Neither raw pending comparison has been treated as already completed. The two
direct extrusion links are retained as self bounds, rather than removed.
They were produced by the actual extrusion bodies; Q has accounted for their
changed store payloads and empty union products.

The opposite experiment explains the exclusion on K. Mapping its old key by q
would give `(o,F(C,D))` before the returned comparison. Native line 101 would
then stop that comparison, leaving U(o) empty. Preserving the raw key is
necessary for the specifically defined native resumption. This is not evidence
that every possible canonical cache design fails.

## 6. Complete native suffix, including activation and replay

The mapped inner App returns Y; its Lambda combines the mapped parameter X
with that result and returns F(X,Y). Recursive completion compares F(X,Y)
below e. Since 1 <= 2, the native right-variable case inserts L(e)=[F(X,Y)];
U(e) is empty. It publishes PolymorphicType(1,e).

The outer E Name at level 1 invokes the native freshener with a new unsigned
memo. It copies e to e' at level 1 and encounters the actual children X/Y of
e's lower Function. Their levels are 1, so the cutoff retains both. There is
no occurrence of raw B/R from which B'/R' could be allocated. e' has lower
F(X,Y), no upper. The original E root and fresh e' are distinct; the map does
not copy Value-reference incidences or create an extrusion occurrence.

The outer App allocates S at level 1 and compares e' below F(A,S). It inserts
that upper and replays e's copied lower. Native Function variance gives
A <: X and Y <: S. A's lower list is empty. Inserting S in U(Y) replays the
retained self-lower Y <: S. The same raw pair is already in this comparison's
cache; that repeated comparison stops. It neither creates a lower of S nor
causes infinite self replay.

The outer Lambda returns F(A,S). Recursive completion inserts that lower in
o, then replays its previously inserted upper F(X,Y). Function variance gives
X <: A and S <: Y. X and S have empty lower lists, so both are ordinary
left-variable upper insertions with no further replay. No further extrusion
or equality event occurs; all four variable endpoints have level 1.

| Owning step | Native comparison(s), insertion and replay |
| --- | --- |
| First App prefix and return | o <: F(B,R); two ordinary polar copies; Q; owed o <: F(C,D) insertion under its second raw key |
| Retained extrusion links | B <: C maps to stored X <: X; D <: R maps to stored Y <: Y; both union products empty |
| E completion | F(X,Y) <: e; insert lower, no opposite upper |
| E Name | One unsigned freshening map; copy e alone, retain X/Y |
| Outer App | e' <: F(A,S); insert upper; replay F(X,Y) <: F(A,S) |
| Function children | A <: X and Y <: S; repeat Y <: S from Y's self-lower, stopped by this call's raw cache |
| O completion | F(A,S) <: o; insert lower; replay F(A,S) <: F(X,Y) |
| Function children | X <: A and S <: Y; no opposite lower |

The full store immediately before final `in odd`, in newest-first list order:

| Row | Level | Lower list | Upper list |
| --- | --- | --- | --- |
| o | 1 | F(A,S) | F(X,Y) |
| A | 1 | empty | X |
| X | 1 | empty | A,X |
| Y | 1 | Y | S |
| S | 1 | empty | Y |
| e | 2 | F(X,Y) | empty |
| e' | 1 | F(X,Y) | F(A,S) |

Every nonempty opposite product here has its owning insertion and explicit
replay in the table. There is no inference from mere storage to activation.
Every bound level is at most its owner level. This covers both completions,
the retained links, all Function children and the self-lower replay; it does
not cover an arbitrary future consumer of these rows.

## 7. Boundary 0 use, compact interface and fixed source principality

O publication remains PolymorphicType(0,o). Its final Name at level 0 uses a
fresh unsigned memo, distinct from both M and E's freshening memo. Traversing
both lists reaches exactly o,A,X,S,Y, all level 1. The native memo is recorded
before copying either list, so each reachable row is copied once, including
self bounds and cycles. The five fresh level-0 rows satisfy:

```text
L(o0)=[F(A0,S0)]       U(o0)=[F(X0,Y0)]
U(A0)=[X0]            U(X0)=[A0,X0]
L(Y0)=[Y0]            U(Y0)=[S0]       U(S0)=[Y0]
all remaining lists empty.
```

e/e' are not reachable from o and are absent from this frame. Source E/O
identities and their separate publication frames have not been collapsed.
All copied bounds have level 0. Neither generalization number nor the native
freshener's cutoff/one-map discipline has been changed.

Positive canonicalization of o0 contributes root variable o0 and its single
lower F(A0,S0). Negative variable closure from A0 is exactly {A0,X0}, with no
nonvariable upper. Positive closure from S0 is {S0}, since S0 has no lower.
The Y0 self-lower is not reachable on that positive result route. Hence:

```text
vars={o0}, fun=(vars={A0,X0} -> vars={S0}), recVars={}
```

Each occurring variable has one polarity, and no compact recursive binding
exists. Native simplification removes all four variables. Coalescing the
empty negative argument produces Top and the empty positive result Bot.
The computed interface is therefore exactly **Theta = Top -> Bot**.

For source typing, under O:Theta and a:Top, temporarily assume E:Theta.
Under inner b:Top, O b has Bot, so E's initializer has Theta. E's body E a
has Bot; O's initializer therefore has Theta. Both original recursive
T-Let rules discharge their assumptions and generalize no free variable;
the final O Name has Theta. This is one coherent derivation in the original
scopes, independently of the store interpretation.

For every finite Fig.3 derivation of the fixed term at tau, peel trailing
subsumption to the outer recursive T-Let with assumption sigma. Its Lambda
initializer supplies X_arg -> X_res <= sigma. The final O Name supplies a
single permitted substitution rho with rho(sigma) <= tau, including all
trailing subsumptions. Substitution preserves the finite subtyping derivation
(freshen recursive binders and substitute all hypotheses together), so:

```text
rho(X_arg) -> rho(X_res) <= rho(sigma) <= tau.
```

Since rho(X_arg) <= Top and Bot <= rho(X_res), Function variance gives
Theta <= rho(X_arg) -> rho(X_res), hence Theta <= tau. Theta is closed;
the identity substitution also witnesses Theta <=_forall tau in the paper's
scheme order. Thus the interface computed by this finite Q continuation is
source typed and principal for this fixed term. No independent marginal
witness selection or general let-polymorphic soundness theorem is used.

## 8. Exact result, remaining bridge and obligation-economy audit

The finite construction goes beyond treating H as an unknown operation:
its cut domain, rewritten slots, class-list construction, untouched historical
records and resumption are explicit. The initial post-store and entire suffix
follow by calculation from those definitions and the actual native bodies.
No contradiction appears for this particular construction and term.

The result remains a bounded theorem about a **proposed mathematical machine**.
Defining Q is not proving that the selected source/compiler operation executes
it. The actual reference has no way to rewrite the suspended App result R or
Lambda parameter B: they are immutable Scala locals. Applying a union to
store rows alone would leave those locals high, construct F(B,R), and fail
to obtain the postcondition needed for section 6. Mathematical equality
does not perform that replacement. A candidate canonical consumer could
instead normalize those locals at use, but its existence and behavior must
be independently established at those consumers.

The smallest still unproved operational bridge is:

```text
At this actual extrusion-return occurrence, an owning constructor consumes
its authentic E/O certificate and two actual polar pairs, then every live
App/Lambda/context/store operand listed in section 3 is interpreted as the
section 4 representative before its next semantic read, while historical
K/M/provenance remain raw and the returned-demand insertion remains owed.
```

The finite source graph can be calculated from resolution and approved
declaration ownership before typing: O -> E,a; E -> O,b; inner Apply result
-> O,b; outer Apply result -> E,a. It requires no inferred ports or bound
edges. That establishes availability of those mathematical source facts for
this term, not an actual early graph/occurrence producer. Definition-root
ownership at publication does not by itself establish an early consumer.

The source/operational bridge shares with the proof the fixed term, resolution,
native prefix, exact event and copies, chosen existing low representatives and
the raw cache discipline. Those are insufficient to establish that an actual
implementation transports live operands. All-source transport, general
activation scheduling, complete Call/effects, abnormal paths and Yulang
reachability are omitted, not hidden in Q's correctness conclusion.

Earlier stock and conditional-quotient attempts left this owning action absent.
The economy audit classifies actual faithful equality/continuation/fresh-use
transport as A/B. Reconstructing occurrence or live-operand ownership after
discarding its construction facts is D. Here the original source and actual
constructor stack already know those facts; a typed event certificate and
canonical reads at the specific constructors are a possible owner-directed
bridge. This note does not adopt that storage design. The finite Q calculation
resolves its own mathematical construction question, while the same A/B
actual-owner premise remains OPEN. Another equivalent quotient note or larger
ground probe would leave that premise untouched.

**One next action:** primary obtains independent review of this frozen finite
construction, then routes the exact App-result/Lambda-parameter canonical-read
bridge above to its owning representation/consumer lane under existing
authority. Any general scheduling/transport decision stays on the primary's
design-authority path; this leaf stops before choosing it.

## 9. Checks, dependencies, resources and runtime

Independent review: `compiler_referee` PASS within this frozen fixed-term
scope, with no BLOCKING, major or minor findings. The reviewer reconstructed
Q, checked the complete live-slot inventory and cache/polarity distinction,
verified every suffix insertion, replay, level and both freshening maps, and
independently checked the native `Top -> Bot` simplification and fixed-term
source principality argument. The review leaves the actual immutable-local
consumer bridge, early certificate producer, all-source properties, Call,
effects, Yulang correspondence and F5 cutover OPEN.

Checks already performed: static rule/source reads with `cat`, bounded `rg`
and `sed`; SHA-256 snapshots; handwritten slot-liveness, union-product, raw-key,
all-comparison/replay, level, both freshening-map and compact-interface
calculations. A final single-process Python integrity check passed all eight
dependency hashes, their snapshot-table entries, and artifact whitespace/newline.
Some broad initial reads truncated and their decisive bodies
were reread in bounded windows. No tests, builds, Scala execution, executable
probes, benchmark samples, Git commands/mutations, compiler/test edits, shared
record edits, question-board edits, other artifact writes or delegation.

At most one lightweight read process was active at once; all commands were
sequential. Zero heavy processes, measurement samples or CPU/RAM reservations.
The wall budget is 30 minutes; exact CPU/RSS and reasoning elapsed time are
unmeasured. The primary remains verification/integration owner. Coverage is one
cut, two class unions, two Apps, two recursive completions, one E-use map and
one O-use map. No arbitrary use history is covered.

Requested runtime: normal Sol/high proof lane (`gpt-6.1-sol/high`) under the
configured unpinned prover role. Observed effective model/effort: unknown;
no effective runtime metadata was supplied to this leaf. Config defaults and
callable prover availability were inspected; neither proves the effective
model, effort or hot reload. No Astra request or child dispatch occurred.

| Direct input | SHA-256 |
| --- | --- |
| Frozen conditional quotient input | `6d2e79c2113562422d06e8250e6830b60fe8b9006b18746b4f23362ac044e6c1` |
| Stock fixed recursive-core proof | `d6366f55b855647303cd0851cbab46036d8180058157f4eae9a2e3445f00c921` |
| Top-level principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| Parent-copy SCC design | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |
| Value/type association | `28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775` |
| Copied-row ownership | `7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd` |
| Reference Typer.scala | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| Reference TypeSimplifier.scala | `618b63f63e71c31890eb36cb18be474bfd31732173c159132306f0e14dc37d2b` |

## Commit packet

* Exact changed/leased path:
  `notes/theory/2026-10-12-fixed-term-quotient-transition-proof.md`.
* Baseline: `5e7ffb735fc1a829d03890ebfd353e17ad7ca342`; direct hashes above;
  no dependency changed by this leaf. Pinned-commit/branch equality and
  integration revalidation are primary-owned; no Git query was run.
* Honest status: independent `compiler_referee` PASS for the provisional finite
  mathematical construction and bounded derivation; no adopted transport
  contract, actual-owner bridge or parent-gate promotion.
* Checks already run: static owners, exact live-slot inventory, both empty
  union products, pending raw key distinction, complete suffix replay/levels,
  both use frames, native Theta interface and fixed source principal argument;
  no tests/builds/probes.
* Proposed one-line checkpoint:
  `research: construct fixed-term extrusion-return quotient transition`.
* Shared-record deltas left for primary/curator: record the explicit finite
  Q construction and its calculated post-store/Theta; retain early certificate
  production, actual live App/Lambda/context canonical reads, all-source
  transport, Call/effect, soundness/principality and F5 parent gates OPEN.
* Writes stop at handoff. Independent review, record synchronization and Git
  integration remain primary-owned.
