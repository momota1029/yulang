# Cross-level recursive core: native final interface and intrusion boundary

Date: 2026-10-12
Status: frozen unreviewed research; finite native derivation and fixed-term
declarative proof, with the intrusion transition OPEN
Assigned baseline: `5817227f32b037f5d957c9bc1ce5accff8e68e5f`
Branch: `research/simple-sub-intrusion`
Reference baseline: `9bae772624c23b52a93c1b226157e16898b4d9db`
Exclusive lease: this file only; leaf, no delegation

## 1. Frozen statement, scopes and claim classes

Fix exactly the original-reference term:

```text
let rec odd = lambda n_outer.
  let rec even = lambda n_inner. odd n_inner
  in even n_outer
in odd
```

This is a pure-core analogue of the user's nested odd/even source, using only
Let/Lam/Var/App. It removes conditional, literals and primitive operations; it
is neither that exact Yulang program nor a source-elaboration/admission theorem.
`odd` is monomorphic throughout its initializer, including the nested binding.
`even` is monomorphic within its own initializer and generalized at its local
publication. Its recursive root is allocated even though its initializer does
not use it. `n_outer` and `n_inner` are distinct binders. The final `even` Name
resolves to the published inner definition; final `odd` resolves to the outer
published definition. No polymorphic recursive use of either open root occurs.

The original parent theorem remains: for every supported source program and
lawful finite inference/use history, with original scopes, complete Call,
effects, attachments, providers, witnesses and residual lineage retained,
actual occurrence-qualified extrusion parent/copy equality preserves source
soundness, required principality and normal inference, and the actual compiler
constructors/consumers implement it. This packet closes no part of that parent
by relabeling its scope.

The subsidiary claims are separately quantified:

1. **Finite native operational derivation:** for this fixed term in a fresh
   reference Typer at level 0 with its builtins, and up to injective renaming
   of allocated identities, unmodified inference produces the schemes/store
   below. Its canonicalize/simplify/coalesce interface is `Top -> Bot`.
2. **Fixed-term declarative proof:** in the paper's Fig. 3 typing system and
   Fig. 10 subtyping, write Theta = `Top -> Bot`. Then `empty |- term : Theta`;
   for every finite derivation `empty |- term : tau`, `Theta <= tau` and
   hence `Theta <=_forall tau`. This is a subsidiary constructive proof
   awaiting independent review, not invocation of a general let theorem.
3. **Approved qualification:** using only the assigned root/Apply incidence
   rules and origin rule, the one actual demand extrusion has origin E,
   receiver O and both pairs `(C,B,+,1)`, `(D,R,-,1)`. Both qualify jointly.
4. **OPEN intrusive execution:** the first unsupported reference transition
   is applying `C=B` and `D=R` before inner publication. The original source
   supplies no such equality consumer. No quotient transition is posited.

Exclusions: arbitrary terms/continuations, Yulang admission/elaboration,
complete Call and effect adequacy, source-wide association/transport,
intrusion scheduling/encoding, abnormal paths, runtime safety and F5 cutover.
No source restriction, new owner law, target retargeting, marginal witness
selection, root-function equality or independently certified status is added.

Falsifiers: an owning reference rule emits a different level, list or replay;
an actual further extrusion is omitted; Fig. 3 admits a derivation violating
the inversion argument in section 5; or the claimed occurrence endpoints do
not follow from the assigned clauses. Stop at the first unsupported intrusive
judgment rather than assume an equality or replay mechanism.

## 2. Exact owners and governing sources

Original source root:
`/home/momota1029/rust/simple-sub-reference`, at the reference baseline above.

| Responsibility | Exact owner |
| --- | --- |
| Term syntax | `shared/src/main/scala/simplesub/syntax.scala:7-14` |
| Recursive root and scheme boundary | `Typer.scala:48-55` |
| Name, Lambda, App, nested Let | `Typer.scala:59-83` |
| Ordered insertion, opposite-bound replay, polar extrusion | `Typer.scala:88-159` |
| Shared use-freshening map and scheme instantiation | `Typer.scala:166-207` |
| Immutable variable levels and bound-level invariant | `Typer.scala:209-227` |
| Direct polar coalescing | `Typer.scala:239-257` |
| Compact/canonical conversion, polar removal, final coalescing | `TypeSimplifier.scala:49-84,102-157,185-239,286-319` |
| Actual display consumer | `js/src/main/scala/Main.scala:73-81`: instantiate, canonicalize, simplify, coalesce |
| Declarative recursive typing and scheme order | local paper PDF, printed pp.4,24,26: Fig.3, Fig.10, section 5.3 |

The paper is *The Simple Essence of Algebraic Subtyping*, DOI
`10.1145/3409006`, local `simple-sub-reference-paper.pdf`. Its scheme order is
`P <=_forall Q` iff some type-variable substitution rho satisfies
`rho(P) <= Q`; more general schemes are on the left. That definition is
available: no missing principality order is invented here. The Scala source
alone supplies syntax/operations, not that declarative judgment.

Governing Yulang clauses: top-level inference principles sections 1-5;
parent-copy SCC design, **Selected operation and compiler responsibility**,
**Nested Apply membership**, **Definition-root Value ownership**, **Retained
boundary**; value/type association, **Approved extrusion-event qualification**
and **Definition-root origin for nested call-demand extrusion**; copied-row
ownership, **Decision**. Read orchestration Model routing/Proof delegation,
research-lab baseline/evidence rules, design authority, compiler-engineering
proof-obligation economy and git-concurrency disjoint-file rules.

The independently reviewed local calculation in
`2026-10-12-odd-even-parent-copy-scc-derivation.md`, section 3, is reused.
It has a nonrecursive inner let; section 3 below explicitly supplies the
recursive-inner difference. Its earlier unresolved association conclusions
are not imported over the later approved occurrence qualification.

## 3. Native recursive-inner extension through both generalizations

Use uppercase solver row names; O and E as source Value roots are separate
objects from solver rows o and e. Function(x,y) is abbreviated F(x,y).
Lists are shown in actual newest-first order; every displayed nonempty list
here contains one member, except o's separate lower and upper lists.

The reviewed prefix allocates o,A at level 1, B,R at level 2 and C,D at level
1. The inner App compares `o <: F(B,R)` and negatively extrudes to `F(C,D)`.
One polar memo creates `(C,B,+)` and `(D,R,-)`; `U(B)=[C]`, `L(R)=[D]`,
`U(o)=[F(C,D)]`. All relevant opposite lists are empty at this cut.

The sole recursive-inner difference is `typeLetRhs(true,even,...)` allocating
e at level 2 before B. No Name returns e in its initializer. On completion
of the inner Lambda, actual `constrain(F(B,R),e)` takes the right-variable
case: `L(e)=[F(B,R)]`. `U(e)` is empty, so no replay or extrusion occurs.
The published scheme is **PolymorphicType(1,e)**, rather than the reviewed
nonrecursive scheme with the Function itself as body.

The outer `even` Name invokes `freshenAbove(1,e)` at level 1. Its one unsigned
memo first creates e', visits e's lower Function and creates B', then R'.
Both level-1 anchors C,D are retained by the early level test. Thus:

```text
e' at level 1: L=[F(B',R')], U=[]
B' at level 1: L=[], U=[C]
R' at level 1: L=[D], U=[]
```

The outer App allocates S at level 1 and compares `e' <: F(A,S)`.
Left-variable insertion stores the demand in `U(e')`, then activates its
existing lower `F(B',R')`. Function comparison generates `A <: B'` and
`R' <: S`. The first stores B' in U(A). The second stores S in U(R') and
replays R's copied lower D, generating `D <: S`, stored in U(D).
Every endpoint and structural demand here has level 1; **no outer extrusion
occurs**, so this outer call creates no additional qualifying pair.

The outer Lambda returns F(A,S). Recursive completion compares F(A,S) below
o, stores `L(o)=[F(A,S)]`, and activates `U(o)=[F(C,D)]`. The actual Function
replay generates `C <: A` and `S <: D`, stored in U(C) and U(S).
Again all levels are 1; no extrusion occurs.

Complete store just before final `in odd`:

| Row | Level | Lower list | Upper list |
| --- | --- | --- | --- |
| o | 1 | F(A,S) | F(C,D) |
| A | 1 | empty | B' |
| e | 2 | F(B,R) | empty |
| B | 2 | empty | C |
| R | 2 | D | empty |
| C | 1 | empty | A |
| D | 1 | empty | S |
| e' | 1 | F(B',R') | F(A,S) |
| B' | 1 | empty | C |
| R' | 1 | D | S |
| S | 1 | empty | D |

There are exactly two Apps in this term. There are no additional generated
constraints, recursive e uses, primitives, selected providers or effect rows.
Each listed active comparison was obtained from its actual opposite-bound
replay. Extrusion's direct links do not themselves enqueue replay; here their
selected copied lists were empty and the later consumers above are explicit.

Outer publication returns **PolymorphicType(0,o)**. Final Name use at level 0
freshens its reachable graph with one memo. The allocation/traversal sequence
is o0, A0, B0', C0, S0, D0: lower o's Function visits A first; A's upper path
visits B' then C and returns the memoized A; S's upper path visits D and
returns memoized S; upper o's Function reuses C0,D0. The result is o0 and:

```text
L(o0)=[F(A0,S0)]       U(o0)=[F(C0,D0)]
U(A0)=[B0']           U(B0')=[C0]       U(C0)=[A0]
U(S0)=[D0]            U(D0)=[S0]
all other lists on these six fresh level-0 rows are empty.
```

Original B,R,e,e',R' are not reachable from o by the actual directed traversal
of both bound lists, and are not freshened by this final use. Reachability
here concerns inference descriptions only and creates no Value-reference edge.

## 4. Final native interface, including coalescing

Direct `coalesceType(o0)` preserves each free row variable and introduces a
negative recursive binder kappa on revisiting A0. Up to association of meets:

```text
alpha_o OR ((mu kappa. alpha_A AND alpha_B' AND alpha_C AND kappa)
             -> alpha_S).
```

The S/D upper cycle does not enter positive result coalescing: S has no lower
bound. This is the direct polar output, not an assertion that every internal
row is equal or that the unguarded binder is semantically collapsed.

The actual simplified display consumer uses `canonicalizeType`, not direct
coalescing. Its negative variable closure at A0 is {A0,B0',C0}; none has a
nonvariable upper. Its positive closure at S0 is just {S0}, with no lower.
Root o0 contributes itself and one lower Function. Hence its compact result
has root variables {o0}, a Function whose argument variables are
{A0,B0',C0} and result variables {S0}, and an empty recursive map.
`compactType` separately gives the same result: its parents test removes
the spurious variable-only revisit at A0 (lines 55-70).

The co-occurrence analysis sees o0 and S0 only positively, and A0/B0'/C0
only negatively. None is a recursive compact variable. Lines 231-239 remove
all five; no co-occurrence unification is needed. Final compact coalescing
maps the empty negative argument to Top and empty positive result to Bot
(lines 308-313). Therefore the fully computed simplified native interface is
**Theta = Top -> Bot**, with no free quantified variable.
This is a hand derivation of the selected consumers; Scala was not executed.

## 5. Direct source soundness and principality of this fixed native output

The original paper **does** contain recursive T-Let in Fig.3. Its premises
are `Gamma,x:tau1 |- rhs:tau1` and
`Gamma,x:forall alpha_i.tau1 |- body:tau2`, with alpha_i not free in Gamma.
Section 5's general proof explicitly excludes let polymorphism; its footnote
15 sketches a duplication route. Neither restriction prevents the following
direct fixed-term proof using the actual declarative rule.

Set Theta = Top -> Bot. Under `odd:Theta,n_outer:Top`, and the unused recursive
assumption `even:Theta`, the inner formal has Top. T-Var and T-App give
`odd n_inner:Bot`; T-Abs gives the inner initializer Theta. Inner T-Let
generalizes no variable and its body `even n_outer` has Bot. Outer T-Abs
therefore gives the complete outer initializer Theta under `odd:Theta`.
Outer T-Let, again with no quantified variable, types final `odd` at Theta.
This proves the exact closed source judgment `empty |- term:Theta`.

For principality, quantify over **every finite Fig.3 derivation** of
`empty |- term:tau`. Peeling trailing T-Sub rules from the outer Let must
reach T-Let; let its recursive assumption be sigma and its final-body type
be eta. Peeling T-Sub from that rule's initializer derivation must reach
T-Abs, since the initializer is syntactically a Lambda. Thus some X,Y satisfy
`X -> Y <= sigma`. This premise uses the same sigma as the outer T-Let;
no root solutions or witnesses are independently selected.

The body is syntactically Var(odd), so peeling its T-Sub rules must reach
T-Var with one permitted substitution rho for the variables generalized in
sigma. Consequently `rho(sigma) <= eta <= tau`.
Fig.10 subtyping is closed under capture-avoiding type substitution: induct
on its finite derivation, substitute every type and hypothesis together,
freshen recursive binders, and observe that substitution commutes with
unfolding and leaves the hypothesis delay/unlocking operators unchanged.
Reflexivity, transitivity, union/intersection, Function and Record rules then
retain their same premises/conclusion. Therefore
`rho(X) -> rho(Y) <= rho(sigma)`.

By Fig.10's empty intersection/union conventions,
`rho(X) <= Top` and `Bot <= rho(Y)`. S-Fun gives
`Theta <= rho(X) -> rho(Y)`. Transitivity gives **Theta <= tau**.
Since Theta is closed, the identity substitution also witnesses
`Theta <=_forall tau`. Together with the explicit typing above, Theta is a
principal interface for this fixed source in the paper's defined order.

This proof does not invoke the paper's unproved general let extension or
runtime progress/preservation. It proves the declarative soundness and
principality of the **stock simplified interface** for one term. It has not
proved that the selected intrusion operation computes or preserves it.

## 6. Qualification, joint equality and the first unsupported transition

Distinguish source roots O,E, formal Values a,b, and Apply-result Values
r_value,s_value from every solver row above. The assigned root rules give
E -> O and O -> E, with formal references E -> b and O -> a. Apply-fragment
ownership gives r_value -> O,b and s_value -> E,a. No source Name targets a
type copy. These clauses alone establish the required O/E SCC across levels;
neither root is identified with an Apply result or a solver port.

The authentic inner call-demand extrusion has origin **E** because the call
belongs to even's initializer, and receiver **O**, its resolved callee.
Its generated polar memo entries are exactly **(C,B,+,1)** and **(D,R,-,1)**.
Thus both belong to the same E-to-O occurrence and jointly qualify for
**C=B and D=R**. The outer call produces no extrusion, as section 3 derives.
Freshening events produce no extrusion pairs and inherit no Value incidence.
No equality `type(O)=type(E)` follows or is imposed.

These equalities are not consequences of the stock source/store constraints.
There is an explicit declarative family under odd:Theta: for fresh independent
beta,gamma, inner `odd n_inner` at Bot can be subsumed to gamma, so the inner
Lambda has `beta -> gamma`. Inner T-Let may generalize beta,gamma because
neither occurs free in odd:Theta or n_outer:Top. Its outer use instantiates
beta=Top,gamma=Bot. This same coherent source derivation permits separate
initializer instances. For example, the stock scalar constraints admit
B=Bot,C=A=B'=Top and R=Top,D=S=R'=Bot, with o=Theta,
e=Bot->Top and e'=Theta. Every Function comparison and level-store constraint
in section 3 is respected at its own original instance. The two proposed
equalities exclude this internal assignment. This is **not** a counterexample
to preservation of the required source principal interface; the approved
operation is not required to preserve every arbitrary pre-intrusion fiber.
The principal exterior was proved separately in section 5.

To execute the operation, however, one must actually apply both equalities
to live rows and their bounds, levels, ports, active comparisons and future
generalization. **That transition has no owning rule in the selected Scala
source.** The first unsupported intrusive judgment is the equality event
after the inner extrusion, before the ensuing E publication/use. Sections
3-4 trace the unmodified baseline past this point; they are not a fabricated
intrusive continuation.

Calling ordinary constrain in both directions does not supply the missing
identity. C and D have immutable level 1; B and R immutable level 2. Even if
`B <: C` and `C <: B` both hold, freshenAbove(1,e) still copies B while
retaining C, using distinct memo identities. The corresponding result issue
holds for R/D. Alias/level/whole-graph replay and equality transport are absent.
In addition, constrain caches `(o,F(B,R))` **before** extrusion at lines
100-102. Simply canonicalizing that in-process key to a returned demand
would make lines 101/123 skip its insertion. Thus a consumer law must cover
pending comparison state, not merely a stored equation or canonical label.
No cache-reset policy or quotient implementation is selected in this note.

The joint typing Theta offers no contradiction to the approved equalities:
choosing all argument endpoints Top and all result endpoints Bot satisfies
them together. Existence of that witness and the stock principal output
do not prove a missing operation's source/consumer adequacy. The requested
intrusion soundness/principality theorem remains **OPEN**, not refuted.

## 7. Obligation economy and next action

Earlier quotient/ground-store calculations and source-owner traces have both
left equality/continuation/generalization transport unresolved. This packet
adds the full native recursive core's final interface and its direct
declarative principal proof, while stopping at that same actual consumer seam.
It does not propose a third equivalent quotient transition.

Faithful equality activation/transport is A/B; event origin/receiver/polar
pairs are known at their source construction, so retaining that certificate
addresses D. Source ownership is already selected for this exact occurrence.
No all-variable owner rule, equality-transport lemma or alternate reconstruction
layer is assumed. The paper's ordinary order is available; its omitted general
let proof is not the first missing premise of this concrete intrusive run.

One next action: assign the owning native equality consumer a bounded
construction/proof packet for this exact live event, including mixed-level
row identity, pending demand/cache state and E generalization/fresh-use
transport; then independent review must connect it to the fixed-term
principal interface. Keep the full parent and Yulang correspondence gates OPEN.

## 8. Checks, resources, runtime and dependency snapshot

Read-only source/rule/PDF inspection, SHA-256 and baseline-content comparison;
one leased note write. No builds, tests, Scala execution, Oracle, executable
probe, benchmarks, Git mutation, question edits, other writes or delegation.
At most four lightweight read commands were submitted concurrently; later
dependency/integrity checks were sequential. Zero measurement samples.
Exact CPU/RAM and reasoning elapsed time were not measured. The primary is
verification/integration owner. Assignment requested normal Sol/high;
effective runtime model/effort metadata is unknown. Prover role keys are
unpinned and configured subagent defaults are Sol/high. No Astra ran or
hot-reload/override success is claimed.

HEAD advanced to `079b66f5cecf8565f895ff9d399e383827cd3394` during work.
All five direct repository inputs below and all five required rule files,
prover config and primary config byte-match assigned baseline `5817227`.
No dependency was edited by this leaf. The reference checkout HEAD matches
its assigned commit; the original bodies were read directly.

| Direct input | SHA-256 |
| --- | --- |
| reviewed parent-copy finite derivation | `238e21c0a027aa9f0ca14c563c3fbaa11188ee268e8b819a049f81dd6afd5830` |
| parent-copy SCC design | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |
| value/type association | `28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775` |
| copied-row ownership | `7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd` |
| top-level inference principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| reference Typer.scala | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| reference TypeSimplifier.scala | `618b63f63e71c31890eb36cb18be474bfd31732173c159132306f0e14dc37d2b` |
| reference syntax.scala | `f26f19f6905d42c247198c45da9b1675b22619dd59749047023efe5f7ee3c60f` |
| reference Main.scala | `1c1a9dd38e0c106b04ce7aca35dab1b5772227bb79836338f1eef52fb6f97258` |
| original paper PDF | `5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698` |

Some initial combined reads truncated; decisive rules, reference bodies and
paper figures were reread in narrow windows. Scope remains static/source and
mathematical, not observed execution. The proof awaits fresh independent review.

## Commit packet

- Exact changed lease: `notes/theory/2026-10-12-cross-level-recursive-scc-core-proof.md`.
- Baseline: `5817227f32b037f5d957c9bc1ce5accff8e68e5f`; reference `9bae772624c23b52a93c1b226157e16898b4d9db`.
- Changed dependency hashes: none; direct hashes above match assigned inputs.
- Claim/review: unreviewed finite native trace and subsidiary fixed-term
  declarative principal proof; missing intrusive transition and parent OPEN.
- Checks already run: source/PDF reads, branch/ref inspection, dependency hash
  and byte comparison; artifact whitespace/integrity check recorded in report.
  Zero builds/tests/probes.
- Proposed checkpoint: `research: derive recursive core principal interface and intrusion boundary`.
- Shared deltas for primary/curator: record stock Theta=Top->Bot, both genuine
  E-to-O pairs jointly qualified, absence of any outer extrusion, and the
  exact equality/cache/generalization consumer premise. Preserve parent,
  complete Call, effects and Yulang source/publication correspondence OPEN.
