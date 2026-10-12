# Fixed recursive core: conditional atomic intrusion continuation

Date: 2026-10-12
Status: independently reviewed conditional research; conditional finite
derivation and localized operational premise; no authoritative
scheduling/transport decision or parent theorem closure
Baseline: `b8a1d3feabf6ace35e9cc02a95843fb2bb8a7f17`
Branch: `research/simple-sub-intrusion`
Reference baseline supplied by the stock proof:
`9bae772624c23b52a93c1b226157e16898b4d9db`
Exclusive lease: this file only; prover leaf, no delegation

## 1. Frozen objective, term, quantifiers and exclusions

Fix exactly the reference term t:

```text
let rec odd = lambda n_outer.
  let rec even = lambda n_inner. odd n_inner
  in even n_outer
in odd
```

The source binders O/E, a/b, and the two Apply-result Values are distinct.
Uppercase type-coordinate names below do not identify those Values. `odd` is
monomorphic throughout its initializer; `even` is monomorphic throughout its
own initializer and generalized at its original boundary 1. Outer publication
has boundary 0. The two formals retain their original lexical scopes. The
extrusion occurrence has origin E, receiver O and actual pairs `(C,B,+,1)`
and `(D,R,-,1)`. Both qualify through the approved O/E Value SCC. No equality
between the definition-root types o/e is imposed.

The primary asks whether the selected equalities C=B and D=R admit a
source-typed finite continuation through both publications and fresh uses
whose principal interface is the stock Theta = Top -> Bot. The original
parent claim still quantifies over every supported source and lawful finite
inference/use history, preserving complete Call, effects, attachments,
providers, witnesses, residual lineages, scopes, soundness and required
principality. This note does not narrow or discharge that claim.

The result here has two separate quantifiers:

1. **Conditional finite continuation.** For this fixed term, fresh reference
   state at level 0, exact stock prefix, and injective renaming of all allocated
   identities, if the atomic state action H below is supplied, every ensuing
   native comparison and level test is admissible, the two specified uses
   finish, and the selected simplified interface equals Theta.
2. **Source conclusion.** For every finite paper Fig.3 derivation of
   `empty |- t : tau`, Theta <= tau and Theta <=_forall tau; also
   `empty |- t : Theta`. The stock proof establishes these source statements.
   Thus the conditional continuation computes that already established
   principal interface; this is stronger evidence than one I/K ground model.

H is an explicit unproved operational hypothesis, not part of an established
theorem or a newly adopted level/cache policy. The approved equality operation
does not yet define this state action. No general downward-level closure,
arbitrary assignment preservation, arbitrary client continuation, runtime
preservation theorem, Yulang admission/elaboration theorem, abnormal path,
complete Call/effect theorem or F5 cutover conclusion is claimed. The full
conditional output is fixed below before deriving its consequences.

Falsifiers: a native owner emits a different comparison or level; a retained
comparison is skipped by the specified literal cache; the final compact
interface differs from Theta; or the claimed early activation/transport H
fails at its actual source owner. The last case invalidates application of
the conditional result, rather than refuting the source principal interface.

## 2. Authority and actual source owners

Governing sections:

- Top-level inference principles sections 1–5.
- Parent-copy SCC design: **Selected operation and compiler responsibility**,
  **Nested Apply membership**, **Definition-root Value ownership**, and
  **Retained boundary**.
- Value/type association: **Approved extrusion-event qualification**,
  **Definition-root origin for nested call-demand extrusion**, and
  **Implementation and proof boundary**.
- Copied-row ownership: **Decision** and **Scope and proof boundary**.

These select occurrence-qualified equality and preserve scope/sharing duties;
they explicitly leave the SCC scheduling point and transport scheme
unselected. The primary's follow-up requests examination of precomputed source
incidences plus immediate qualified pair unions, with no adoption assumed.

The actual reference is
`/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/`:

| Responsibility | Exact source |
| --- | --- |
| Recursive roots and publication | `Typer.scala:48–55` |
| Var/Lam/App/Let constructors | `Typer.scala:59–83` |
| Literal raw comparison cache | `Typer.scala:88–103` |
| Function variance, insertion, replay and returned extrusion demand | `Typer.scala:106–126` |
| Polar extrusion memo, direct parent/copy links | `Typer.scala:134–156` |
| One unsigned map per use | `Typer.scala:166–188,199–202` |
| Immutable levels and bound invariant | `Typer.scala:209–227` |
| Raw variable identity/hash | `Typer.scala:223–233` |
| Canonical variable closure | `TypeSimplifier.scala:102–157` |
| Single-polarity variable removal | `TypeSimplifier.scala:185–239` |
| Empty negative/positive coalescing | `TypeSimplifier.scala:286–319` |

There is no equality-state constructor in these reference bodies. The earlier
candidate owner audit identifies an implemented candidate law, but that law
is not used as a semantic premise here. In particular no candidate minimum
level update, recapture predicate, relation-generation rule or type-SCC graph
is adopted.

## 3. Source graph availability: a fixed-term lemma, with its boundary

Resolve the original syntax under its lexical binders before examining type
coordinates. The approved definition-root and Apply-fragment rules yield:

```text
O -> E, a
E -> O, b
inner Apply result -> O, b
outer Apply result -> E, a
```

The nested E initializer belongs to E, so its `odd` occurrence is not
forwarded as an O-owned reference. The final `in odd` lies outside the outer
initializer. Neither an Apply containment edge nor a reference to a copied
type is inserted. E's unused recursive assumption emits no Name occurrence.

For these rules all targets follow solely from resolution and declaration
ownership. No type comparison, level, provider selection, inferred function
port or extrusion copy is needed to calculate the listed incidences. The
two root paths O -> E and E -> O already prove equality of the two root SCCs;
adding other legitimate incidences cannot destroy those paths. Therefore the
qualification of this one occurrence can be known mathematically before
constraint propagation, once these resolved source facts are available.

This establishes a fixed-term *source-data availability* lemma, not that the
current reference emits that graph early. The approved root rule says the
root owns its references at publication; computing the same source-only
incidences beforehand is a proposed phase ordering. The reference contains
no Value-graph producer/SCC prepass at all. The approved Apply rule leaves
Lambda/Block/wrapper boundaries outside its scope, and this lemma does not
prove complete precomputation for those constructors, effects, alternatives,
or the full Yulang source domain. No new owner convention is inferred.

At the abstract graph level immediate processing of this event qualifies
exactly its retained pairs, so it implements the selected *activation test*.
That fact alone does not justify its timing relative to native comparison
completion, publication or freshening. The remaining premise is H.

## 4. Atomic action H and the exact pending cache test

Stock allocation gives o,A at level 1 and e,B,R at level 2. The first App
calls `constrain(o,F(B,R))`, where F is Function. Its owning cache K inserts
the literal pair `(o,F(B,R))` at lines 100–102 before extrusion. Negative
extrusion produces C,D at level 1, with direct links `U(B)=[C]` and
`L(R)=[D]`, and polar memo entries `(B,+)->C`, `(R,-)->D`.

Examine the following proposed atomic action, applying each actual pair after
its native direct link and selected copied bounds have been constructed
(lines 150–151 or 153–154), before that variable case returns at line 156.
Both pair actions therefore finish before returning the transformed Function
demand:

```text
q(B)=C, q(R)=D; q is identity on every other type coordinate.
X denotes the existing level-1 row C, representing [B=C].
Y denotes the existing level-1 row D, representing [R=D].
```

H has exactly these responsibilities:

1. The source-only graph is available and this actual occurrence activates
   the two qualified equalities at this point.
2. Union both bound sides of each class, rewrite active type operands and
   future bound consumers by q, and transport the live source typing context
   and suspended Lam/App results by the same q. Thus the original formal
   `n_inner` and its App result subsequently use X/Y. Original source binders
   and all historical allocated identities remain distinct records.
3. Use the already existing immutable level-1 anchors X/Y in those live
   operands. Do not introduce a new row, mutate another row's level, impose
   another equality, or perform a downward dependency closure. Re-embed
   active Function descriptions with those actual children so their native
   maximum-child level is correct.
4. Preserve K's literal raw key `(o,F(B,R))` and the polar memo's original
   keys/parent provenance. These historical raw identities are not canonical
   semantic class keys. Continue the original extrusion comparison with the
   returned raw Function `F(C,D)` through the native `constrain` owner.

Items 2–3 are the missing live-state quotient/level-transport judgment. They
are not supplied by mathematical equality alone: Scala's variables and the
suspended constructor's local bindings have immutable levels/values and no
equality transport operation. The low-anchor representation is examined as
one finite realization, not selected as the general level policy. Original
level-2 B/R remain in historical event/cache records; they are not newly
generalized live coordinates. Actual captured-context transport is required,
rather than silently changing only the printed names.

Item 4 preserves the *actual* native cache law. Raw B,C are distinct
Variable allocations, as are R,D. Function's case-class key compares its raw
children; Variable supplies no semantic-class equality. Consequently:

```text
K = {(o,F(B,R))}
(o,F(C,D)) not in K
```

The recursive call at line 123 therefore adds `(o,F(C,D))` and inserts
`F(X,Y)` in U(o) normally. No pending comparison is declared complete, no
cache reset is assumed, and no replay is skipped. The same cache now contains
both literal pairs until its owning call returns. The polar memo retains
both actual produced pairs without making freshening another extrusion.

If instead the earlier key were rewritten to `(o,F(C,D))`, line 101 would
return before the only insertion at line 116. Then U(o) would remain empty.
This is a precise counterexample to *canonicalizing the pending key and
re-entering the ordinary cached comparison*. It is not a contradiction to the
selected equality operation or the literal-key H examined here.

Thus immediate union before the transformed comparison does not by itself
remove the pending-key issue. The raw historical versus live operand
distinction is decisive. The reference's cache specifies the former; the
unprovided intrusion state action must preserve it while transporting the
latter. This note proves the literal cache calculation conditional on H;
it does not prove that an actual equality constructor implements H.

## 5. Complete finite continuation under H

At the end of the first App comparison the active store is:

```text
level 1: o,A,X,Y
level 2: e
U(o)=[F(X,Y)]   U(X)=[X]   L(Y)=[Y]
all other lists empty.
```

Both original links are retained as reflexive bounds. X has no lower and
Y no upper, so neither class union has a nonempty lower/upper cross-product.
No constraint has been omitted on the ground that it is merely stored.
Neither equality requires high descendants to lower in this pure term.

The actual inner Lam now returns F(X,Y). Inner recursive completion calls
`constrain(F(X,Y),e)`: its level is 1 <= 2, so the right-variable case
stores `L(e)=[F(X,Y)]`; U(e) is empty. E publication is still precisely
`PolymorphicType(1,e)`.

The E Name use at level 1 uses one native `freshenAbove(1,e)` map. It copies
e once to e' at level 1, while both actual children X/Y have level 1 and
are retained by the early level test. No B'/R' are allocated in this
continuation:

```text
e' at level 1: L=[F(X,Y)], U=[]
```

This is derived from H plus the real freshener; the stock post-event B'/R'
allocation cannot be imported unchanged. Copies remain description frames;
e and e' are distinct. No Value incidences or new pair records are copied.

The outer App allocates S at level 1 and calls `constrain(e',F(A,S))`.
It stores that upper and replays e's copied lower Function, generating
**A <: X** and **Y <: S** by the native Function variance rule. A's lower
list is empty. Y's lower list contains Y, so insertion of U(Y)=[S] replays
`Y <: S` once more. That literal pair was already inserted in this call's
cache before its insertion; the repeated comparison returns at line 101.
There is no infinite self-bound replay and no omitted nonreflexive demand.

The outer Lam returns F(A,S). Outer recursive completion calls
`constrain(F(A,S),o)`, inserts the lower and replays the previously retained
F(X,Y) upper, generating **X <: A** and **S <: Y**. Neither X nor S has a
lower, so no further replay is generated. All four comparisons have level-1
endpoints and use native left-variable insertion; no further extrusion occurs.

Every generated direct/replayed comparison is now listed:

| Owner or event | Comparison and actual consequence |
| --- | --- |
| First App | `o <: F(B,R)`; negative extrusion; returned `o <: F(X,Y)` inserted with two distinct literal cache keys |
| Positive parent link | `B <: C`, becoming retained `X <: X`; no lower/upper cross-product at union |
| Negative parent link | `D <: R`, becoming retained `Y <: Y`; no lower/upper cross-product at union |
| E completion | `F(X,Y) <: e`; right-variable lower insertion, no upper replay |
| Second App | `e' <: F(A,S)`; left-variable upper insertion |
| Its Function replay | `F(X,Y) <: F(A,S)`, giving `A <: X` and `Y <: S` |
| Y self-lower replay | `Y <: S` repeated, stopped by that call's literal cache |
| O completion | `F(A,S) <: o`; right-variable lower insertion |
| Its Function replay | `F(A,S) <: F(X,Y)`, giving `X <: A` and `S <: Y` |

Complete active store before the final Name:

| Row | Level | Lower list | Upper list |
| --- | --- | --- | --- |
| o | 1 | F(A,S) | F(X,Y) |
| A | 1 | empty | X |
| X | 1 | empty | A,X |
| Y | 1 | Y | S |
| S | 1 | empty | Y |
| e | 2 | F(X,Y) | empty |
| e' | 1 | F(X,Y) | F(A,S) |

List order is newest first. The two X bounds include the original self-upper;
the Y self-lower is retained. No third owner exists here with unactivated
opposite bounds: e/e'/o are the only structural owners, and their relevant
products were explicitly driven by insertion. The j/V seam of the primitive
ground model is absent from this exact term, rather than assumed solved.

## 6. Levels, both boundary frames and final principal interface

At each stage every bound's level is at most its owner's level. The initial
two class lists consist only of their own level-1 anchor. Subsequent A/X/S/Y
bounds have level 1; F(X,Y) and F(A,S) have level 1; e has level 2 and e'
and o level 1. No level-2 bound is installed in a level-1 row. This proves
the fixed leveled-store consequence of H without a closure algorithm.

Boundary 1 copies just e and captures X/Y once as the already shared live
coordinates. An additional E use with a separate memo would copy a distinct
root and retain those same anchors; aliases of one e' retain its one root.
That observation checks the map partition; arbitrary new use constraints
are outside the frozen continuation theorem. Source binders, lexical boundary
numbers and the actual initialization event have not been changed.

Outer publication is still `PolymorphicType(0,o)`. Its specified final Name
uses a new unsigned memo. Following both bound lists from o reaches exactly
o,A,X,S,Y. All five have level 1 and therefore are copied to level 0. The
memo creates o0,A0,X0,S0,Y0 and preserves the self bounds and cycles:

```text
L(o0)=[F(A0,S0)]       U(o0)=[F(X0,Y0)]
U(A0)=[X0]            U(X0)=[A0,X0]
L(Y0)=[Y0]            U(Y0)=[S0]       U(S0)=[Y0]
all remaining lists empty; all five rows level 0.
```

The memo is inserted before copying a row's lists, so all revisits return
the corresponding single fresh identity. e/e' are not reachable from o
and are not copied into this frame. No original E frame is identified with
the O frame. Every copied bound has level 0, proving this fresh use lawful.

Native positive canonicalization of o0 contributes root variable o0 and
its sole lower F(A0,S0). Negative variable closure from A0 is {A0,X0};
there is no nonvariable upper there. Positive closure from S0 is just {S0}
because S0 has no lower. Y0's self-lower is not on this selected positive
route. `canonicalizeType` therefore produces exactly:

```text
vars={o0}, fun=(vars={A0,X0} -> vars={S0}), recVars={}
```

All four occurring variables have a single polarity and none is recursive
in the compact representation. Native simplification removes them. Empty
negative/positive compact children coalesce respectively to Top/Bot. The
final displayed interface is **Theta = Top -> Bot**.

The stock proof's direct source derivation has the same original scopes:
under odd:Theta and n_outer:Top, assume the unused recursive even:Theta;
under n_inner:Top the call odd n_inner has Bot; E's initializer is Theta;
its body even n_outer has Bot; O's initializer is Theta; final odd has
Theta. Both T-Let boundaries generalize no free variables in this derivation.
It is one joint source derivation, not independent marginal witnesses.

For principality reuse the stock proof's universal inversion argument:
every finite typing `empty |- t:tau` contains an outer initializer arrow
X_arg -> X_res below its one recursive assumption sigma. The final Name
uses one permitted substitution rho with rho(sigma) <= tau. Substitution
preserves the finite subtyping derivation; Function variance, X_arg <= Top
and Bot <= X_res give Theta <= rho(X_arg)->rho(X_res) <= rho(sigma) <= tau.
Theta is closed, so it also precedes tau in the paper's scheme order.
Thus the computed interface under H is source typed and principal for the
fixed term. Neither a finite I/K substitution nor an all-source inference
theorem is used as a substitute for this conclusion.

## 7. Established versus missing premises; actual bridge status

| Premise | Evidence/status |
| --- | --- |
| Original allocations, two polar pairs and scalar prefix | Stock finite source-owner derivation; direct reference owners |
| E/O origin/receiver and same Value SCC | Approved root ownership/origin clauses; fixed source path calculation |
| Source incidences independent of constraint propagation for this term | Fixed-term lemma in section 3 |
| Literal old/new pending cache keys are distinct | Actual reference raw cache/Variable/Function identity; section 4 |
| Native continuation comparisons, levels, two map frames, final Theta, under H | Complete handwritten conditional derivation, sections 5–6; independent compiler_referee PASS |
| Source typing and principal order of Theta | Previously established stock fixed-term source proof, reproduced only as its application |
| An actual producer makes the Value graph available before propagation | Missing; no reference Value-graph/SCC prepass |
| An actual equality owner realizes H on contexts, suspended results, structural levels and historical cache/memo identity | Missing; no reference equality-state rule |
| All-source soundness, principality, Call/effects, Yulang correspondence | Original parent gates remain OPEN |

This advances the mathematical fixed-term feasibility question: boundary-1
anchor reuse need not lose its principal exterior, and the exact changed
allocation trace can be derived all the way to the final interface. It
does not advance the *actual source-to-implementation theorem* past its first
missing construction. The candidate owner audit still lacks an approved
occurrence certificate/activation consumer; no current code was changed or
assumed to emit H. Immediate union with a precomputed graph is an examined
construction, not a derived general scheduling law or adopted durable contract.

The pending-key calculation also limits the proposed ordering: its success
requires preserving historical raw cache keys. A proposal that simply rewrites
all state, including those keys, has the concrete failed-insertion execution
in section 4. Timing alone does not prove cache adequacy.

Obligation-economy audit: earlier stock/source-owner and candidate scalar
passes left the live equality/publication operation missing. This note
changes method by deriving the entire changed native continuation and testing
the actual pending cache. The remaining transport/activation premise is A/B,
not an optional stronger characterization. Occurrence identity, resolved
origin/receiver and actual pairs are known at construction and should be
retained there; recovering them later is D. Neither classification closes
the original gate. A further ground model or equivalent quotient restatement
would leave the same missing owner untouched and should not be the next lane.

**One next action:** construct the exact native operational judgment at
`constrain`'s extrusion-return seam (`Typer.scala:121–123`) for this one
occurrence: consume the source-backed E/O certificate, transport the live
Lam/App context to the existing level-1 anchors, preserve the two literal
pending keys and original polar provenance, and return the F(C,D) comparison
to the owning insertion. Its postcondition is precisely section 5's cut
store and unchanged source scopes. Prove this judgment from the chosen
state representation before using this conditional continuation to close a
fixed intrusive-execution gate. The primary must adjudicate any newly
selected scheduling/transport contract and assign independent proof review.

## 8. Dependencies, checks, resource use and commit packet

Independent review: `compiler_referee` PASS, no BLOCKING, major or minor
findings. The reviewer independently reconstructed the source-incidence
boundary, polar pairs, literal cache distinction, replay trace, both freshening
frames, final canonical interface, and fixed-term source typing/principality.
The review explicitly leaves H, early graph production, its realization,
all-source preservation, Yulang correspondence, Call/effects, and cutover OPEN.

Direct dependency SHA-256 snapshots:

| Input | SHA-256 |
| --- | --- |
| Top-level inference principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| Parent-copy SCC decision | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |
| Value/type association | `28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775` |
| Copied-row ownership | `7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd` |
| Stock fixed-term proof | `d6366f55b855647303cd0851cbab46036d8180058157f4eae9a2e3445f00c921` |
| I/K ground-model proof | `4b9d43a1af9454dcd569b53eb293b2a342b81c8a3b404e2cd32d12950ce8b443` |
| Fixed merge falsification | `a07fb12347ee33c1a9302e6b612fa6071210b026fab585c1605d4f3ef38afc2e` |
| Consumer-law owner audit | `f4b5dfebe1eff301f248279e4d52a4234e17a6f7d1fb0b904f44b7055dc646cb` |
| Reference `Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| Reference `TypeSimplifier.scala` | `618b63f63e71c31890eb36cb18be474bfd31732173c159132306f0e14dc37d2b` |

Checks are static rule/source inspection using `cat`, bounded `rg`, `sed`
and `nl`; SHA-256 snapshots; artifact whitespace/scope inspection; the
complete hand comparison, level, map and compact-interface calculations.
No executable model, tests, builds, probes, performance measurements,
implementation edits, shared-record edits, subagent dispatch, external
contact or Git mutation occurred. Two initial read-only Git HEAD/branch
queries were run despite the packet's no-Git exclusion; no further Git
command was used. Baseline integration and revision revalidation remain
the primary's responsibility.

Only lightweight static command processes ran; no heavyweight process,
measurement samples or CPU/RAM reservation. The lane is bounded to 30 minutes;
exact CPU/RSS and reasoning elapsed time are unmeasured. One native occurrence,
two pair unions, two Apps, two recursive completions, one E-use memo and one
O-use memo are covered. No arbitrary future constraint history is covered.

Requested runtime: normal `gpt-6.1-sol/high` proof lane under configured
unpinned prover role. Observed effective model/effort: unknown; no runtime
metadata was supplied. No Astra assignment or further delegation occurred.
No reload or effective override is claimed. The callable schema lists prover;
the role file omits model/effort pins and config defaults name Sol/high.

Commit packet:

- Exact changed/leased path:
  `notes/theory/2026-10-12-fixed-term-intrusion-quotient-proof.md`.
- Baseline: `b8a1d3feabf6ace35e9cc02a95843fb2bb8a7f17`; direct dependency
  hashes above, unchanged in the handoff recheck; no input edited by this leaf.
- Review status: independent compiler_referee PASS; conditional continuation
  and raw-cache discriminator; no parent-gate promotion.
- Checks already run: static owners, all finite comparisons and replay,
  level invariant at each stage, both map frames, native compact interface,
  application of stock principal source theorem; zero tests/builds/probes.
- Proposed checkpoint message:
  `research: derive conditional fixed-term atomic intrusion continuation`.
- Shared-record deltas for primary/curator: record the conditional boundary-1
  anchor-reuse continuation and final principal Theta; retain H, early
  Value-graph producer, actual occurrence activation and source/compiler
  correspondence OPEN; preserve original parent theorem/Call/effect/cutover
  gates. No shared file was edited.
- Writes stop on handoff; independent review and all Git integration belong
  to the primary.
