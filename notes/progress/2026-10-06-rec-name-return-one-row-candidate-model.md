# A candidate satisfaction model for one recursive member-use row

Date: 2026-10-06
Status: independently reviewed research-only candidate model and symbolic derivation
Pinned baseline supplied by primary: `1e49e88f07fa8ceb0b05d109bab6c6a1f23d8d87`
Exclusive write lease: this file only
Method: construct a regular-tree carrier, prove its order laws, and calculate a satisfaction fiber
Implementation authority: none

## Objective, authority, and claim boundary

Give a mathematical interpretation to the isolated incoming graph left open
in `2026-10-06-rec-name-return-purefun-production-reduction.md`, for either
member of `my f x = g; my g y = f`. The initial graph has one fresh binder
row `rho`, one consuming row `c`, and the exact lower term
`L = Fun(Top,Fun(Top,rho))`. Its three obligations are

```text
L <= rho       rho <= Top       L <= c.
```

The governing sections are the redesign charter §§1–4; candidate pure source
rules, “Semantic fragment”; the member-scheme bridge, H1–H4 and “Audit of the
two witness shifts”; and the production reduction, “Exact named scheme and
incoming-use reduction” and “Smallest residual H4 premise”. The three rules
`research-lab.md`, `design-authority.md`, and `git-concurrency.md` govern
research status, frozen dependencies, leases, and primary integration.
`notes/design/INDEX.md` was used only as a locator. Narrow current-task and
laboratory-seed searches supplied context, not new semantic premises.

The primary's accepted boundaries stay fixed: F5 is comparison material;
candidate RecGroup is not selected Yulang semantics; arbitrary successful
concrete endpoint comparisons do not compose into this preorder. The charter
leaves denotation unselected. No question or approval bundle is consumed.

**Candidate assumptions:** choose the structural carrier below, interpret
both polarities of a row by one assigned value, and interpret its retained
bounds as simultaneous inequalities. These choices are research hypotheses.

**Mathematical results within that candidate:** the carrier has greatest Top
and a total Function constructor satisfying the complete variance law;
the isolated graph has the stated exact fiber; and its existential target
projection is calculated below. These derivations are unreviewed. They are
not established production results or an independently certified theorem.

**Still conditional:** applying these results to the solver requires both
directions of a realization/denotation bridge. H4 of the member-scheme bridge
remains open. No solver diagnostic completeness, source acceptance, runtime
soundness, principality for Yulang, or implementation authority is claimed.

## A complete structural regular-tree carrier

Let `D` be the set of rooted regular trees over the ranked signature

```text
Bottom, Top, Int : arity 0
Fun             : arity 2 (argument, result).
```

A regular tree is the unfolding of a finite rooted labelled graph with the
specified arities. Presentations with the same unfolded tree are identified.
Graphs may have cycles; every visited node has a constructor label. There
are no unlabelled recursive aliases. `Fun(A,R)` joins a fresh Function root
to presentations of `A` and `R`. This is defined for every pair in `D`, and
the resulting tree is regular. Bottom and Int are research atoms, not an
assertion about production syntax or runtime values.

For any binary relation `X` on `D`, define the monotone operator

```text
(s,t) in Phi(X) iff
  s = Bottom
  or t = Top
  or s = t = Int
  or [s = Fun(a,r), t = Fun(b,q), (b,a) in X, (r,q) in X].
```

Define `<=` to be the greatest fixed point of `Phi` in the powerset lattice
of `D x D`. Thus `<= = Phi(<=)`. Coinduction means that any relation
`X subseteq Phi(X)` is contained in `<=`. This is a definition of a research
relation, not an assumed transition specification of the production solver.

Reflexivity follows by coinduction on the identity relation: atom pairs use
the atom/Top/Bottom clauses, and a Function pair has identity child pairs.
Bottom is least and Top greatest directly from their clauses.

For transitivity put

```text
X = { (s,t) : exists m. s <= m and m <= t }.
```

Show `X subseteq Phi(X)`. If `s=Bottom` or `t=Top`, the terminal clauses
apply. Otherwise a middle Bottom would force `s=Bottom`, and a middle Top
would force `t=Top`, by inversion of the fixed-point equation. A middle Int
forces both endpoints Int. A middle Function forces both endpoints Function:
writing them `Fun(a,r)`, `Fun(b,q)`, `Fun(d,z)`, respectively, gives

```text
d <= b <= a       r <= q <= z.
```

Their reversed argument pair `(d,a)` and result pair `(r,z)` belong to `X`.
This establishes the Function clause of `Phi(X)`. Coinduction proves
transitivity without assuming it for the child compositions.

Finally neither Function endpoint is Bottom or Top, so fixed-point inversion
and the Function clause give the complete law, for every `A,R,A',R' in D`:

```text
Fun(A,R) <= Fun(A',R') iff A' <= A and R <= R'.
```

This proves H1–H2 internally to the candidate. It does not identify the
candidate relation with the endpoint-dependent production relation.

## Valuations and the complete fiber

Let a valuation `nu` assign one element of `D` to every live value row under
observation. Both `v+` and `v-` evaluate to `nu(v)`. The candidate evaluation
of Top is Top; evaluation of either pure polarized Function uses its recorded
value argument and result through total `Fun`. The matched pure effect leaves
are absent from this model: their production elimination is an input from
the audited reduction, not a theorem about general effects.

Term evaluation stops at a row handle and looks up its assigned value. In
particular, evaluating the finite syntax `L` does not recursively evaluate
the lower bounds stored on `rho`. A cyclic bound is an inequality over the
chosen value, not a recursive equation imposed by syntax evaluation.

For a bound graph `C`, define

```text
Sat(C) = { nu : for every retained l <= u in C,
                   eval(l,nu) <= eval(u,nu) }.
```

The bounds stored on row `v` require every lower to be below `nu(v)` and
`nu(v)` to be below every upper, all under the same valuation. A row's local
bound fiber is not automatically the global fiber: terms stored on other
rows can also contain `v`.

More precisely, with all coordinates except `v` held by `eta`, the complete
satisfaction fiber is

```text
Fib_C,v(eta) = { d in D : eta[v := d] in Sat(C) }.
```

All retained obligations are tested, including occurrences of `v` nested in
another row's lower. No independent choice is made for different occurrences
or polarities of `v`. This addresses the essential sharing requirement of
the one-row premise.

For the isolated graph `C0`, hold `nu(c)=U` and hide only `rho`. Put
`F(t)=Fun(Top,t)` and `G(t)=F(F(t))`. Direct evaluation, with no elimination
or solver assumption, gives exactly

```text
Fib_C0,rho(U) = { d : G(d) <= d and d <= Top and G(d) <= U }
             = { d : G(d) <= d and G(d) <= U }.

P(U) iff Fib_C0,rho(U) is nonempty.
```

The second equality follows from greatestness. The predicate-to-use clause
is `G(d)<=U`; neither `d<=U` nor a direct `rho->c` edge has been substituted.
Also `G(d)<=d` does not require `d=G(d)`: `d=Top` satisfies it strictly,
because `Top` is not below `G(Top)`.

This is the exact denotation of the declared candidate graph by definition
and evaluation. It does not prove that the mutable solver row has that
denotation or that every candidate witness is production-realizable.

## Calculate the isolated projection

There is a regular element `Omega` with

```text
Omega = Fun(Top,Omega).
```

Its presentation has a Function node whose argument points to a Top node
and whose result points back to itself: two nodes suffice. Consequently
`F(Omega)=G(Omega)=Omega`. This explicit candidate element is not inferred
by treating the row's stored lower as an equation.

For a tree `t`, its result spine repeatedly follows only Function-result
edges. Call this spine safe if it either reaches Top or continues through
Functions forever, without reaching Int or Bottom. Arbitrary Function
argument trees are permitted.

**Spine lemma:** `Omega <= t` iff the result spine of `t` is safe.
For the forward direction, fixed-point inversion at a Function reduces the
comparison to its result, because its argument is below Top. At a finite
Int/Bottom terminus the comparison is impossible. For the reverse direction,
let

```text
X = {(Omega,t): t has a safe result spine} ∪ {(s,Top): s∈D}.
```

Every pair in the second set satisfies Phi by its Top-target clause. For a
pair `(Omega,t)` in the first set, if `t=Top` it is already covered; otherwise
safety means `t=Fun(A,R)` with a safe result spine for `R`. The Function
clause requires `(A,Top)` and `(Omega,R)` in `X`; the first is in the second
set and the second is in the first. Thus `X⊆Phi(X)`, so coinduction proves
the comparison, including an infinite spine. No induction on an infinite tree
is used.

**Postfixpoint lemma:** `G(d)<=d` implies `Omega<=d`.
If the result spine of `d` first reaches Int or Bottom after `k` Function
edges, decompose `G(d)<=d` along those `k` result edges. At that address the
right side is the atom, while the left side is a Function: for `k<2` it is
one of the two prefixed Functions; for `k>=2` it is the result subtree of
`d` at address `k-2`, before its first atom. Neither Function/Int nor
Function/Bottom is admitted by `Phi`. This contradicts the assumed
comparison. Therefore the spine is safe, and the spine lemma applies.

In particular Omega is a least postfixpoint of G in this candidate preorder:
it is itself a postfixpoint and is below every postfixpoint. This conclusion
is derived from this carrier's structural rules. It is not supplied by H1–H2
alone or asserted as the denotation of a solver binder.

The full isolated projection can now be calculated:

```text
For every U in D, P(U) iff Omega <= U.                    (T)
```

If `P(U)` has witness `d`, the postfixpoint lemma gives `Omega<=d`.
Monotonicity of G, which follows twice from the complete Function law, gives
`Omega=G(Omega)<=G(d)<=U`. Conversely, if `Omega<=U`, choose `d=Omega`;
both fiber inequalities hold. This proves both directions, over all regular
targets in the declared carrier, rather than only finite syntax targets.

Examples follow symbolically: `P(Top)` and `P(Omega)` hold; `P(Int)`,
`P(Bottom)`, and `P(Fun(Int,Int))` fail; `P(Fun(Int,Top))` holds.
The target must have a safe result spine; its argument trees do not constrain
this existential projection. Top is a valid binder witness at target Top
but is not a valid binder witness at target Omega, since
`G(Top)<=Omega` would imply `Top<=Omega` after two result decompositions.

For the exact two-Function replay shape of the production reduction,
set `U=Fun(A0,Fun(A1,V))`. The complete Function law gives

```text
G(d) <= U iff A0 <= Top and A1 <= Top and d <= V
           iff d <= V.
```

Thus its complete fiber is `{d : G(d)<=d and d<=V}` and is nonempty iff
`Omega<=V`. This provides an explicit candidate meaning of the live residual
comparison, while leaving its algorithmic diagnostic behavior unproved.

## Caller and session constraints must survive the projection

For a caller relation `K(d,U,eta)`, the correct observed relation is

```text
P_K(U,eta) iff exists d.
  G(d) <= d and G(d) <= U and K(d,U,eta).
```

It is generally invalid to replace this with
`P(U) and exists d.K(d,U,eta)`: the two existential witnesses may disagree.
If K is independent of d, the separation is valid; otherwise it requires
a separate proof. Session constraints connecting several incoming instances
likewise belong inside their joint existential relation. Distinct allocated
row identities permit independent coordinates, but do not prohibit a caller
from relating those coordinates.

A minimal added-obligation separator for this declared graph is

```text
U = Top
K(d,U) = (d <= Int).
```

The isolated projection is true, with `d=Omega`. K by itself has witness
`d=Int`. The complete fiber is empty: inversion of `d<=Int` forces d to be
Bottom or Int, whereas `G(d)` is a Function and cannot be below either.
One additional ground upper bound on the hidden row suffices. Removing that
upper restores a witness; removing the cyclic lower also restores a witness
`d=Int`. This is a smallest witness by number of added nonredundant
inequalities relative to fixed C0: zero additions cannot distinguish C0
from itself. No global minimality across other graph encodings is claimed.

The example is a mathematical session extension, not a claim that the exact
source fixture generates that extra upper. When a caller upper on c really
is `Fun(A0,Fun(A1,Int))`, the preceding decomposition already represents the
restriction in the target and correctly rejects it. The separator concerns
an obligation outside the chosen U observation.

Additional bounds solely on c can also be retained correctly. For example,
if the observation is a ground upper V rather than an assigned row value,
the relation is `exists U,d. G(d)<=d and G(d)<=U and U<=V`. Transitivity
and choosing `U=Omega,d=Omega` show that it is equivalent to `Omega<=V`.
This is a proved special case, not permission to erase arbitrary caller
relations or shared outer anchors.

## Candidate transport versus solver realization

Within this candidate preorder, adding a replay obligation `l<=u` from
retained `l<=v` and `v<=u` preserves Sat, by transitivity. Decomposing a
pure Function comparison into reversed arguments and covariant results
preserves Sat in both directions, by the complete law. These are conditional
preservation facts about the declared interpretation. They establish no
whole-session production transition theorem.

The remaining production bridge must establish, for the actual admitted
target observations and complete caller/session graph, that candidate
assignments and actual member instances correspond in both directions.
It must account for row ownership, both polarities, nested occurrences,
retained obligations, level changes, replay, memoization and diagnostic
completion. It must justify which arbitrary carrier targets are representable
or observable. Production's missing positive Top constructor, admission of
typed pairs, and availability/diagnostic distinction cannot be discharged
by choosing this abstract D. A source/runtime adequacy theorem is a further
obligation, even after a solver realization theorem.

In particular the coinductive definition above is not evidence that cyclic
pair memoization implements that definition. A finite checker using Phi
would only check consequences of Phi. It could not prove that Phi supplies
the intended Yulang source relation. The candidate's consistent carrier
reduces an existence question and makes the isolated fiber concrete; it does
not close H4 for production.

## Independent review and proof repair

A first read-only compiler-referee review found a major gap in the reverse
Spine-lemma coinduction: the relation containing only `(Omega,t)` pairs omitted
the required `(argument(t),Top)` child pairs. The proof was repaired by adding
all target-Top pairs to the postfixed relation. A fresh compiler-referee review
then checked the revised coinduction and dependent postfixpoint/projection
claims and found no blocking, major, or minor findings. It also checked the
carrier laws and caller-separator derivation. This review certifies only the
mathematics over the declared candidate regular-tree carrier; the bidirectional
solver realization and all Yulang authority remain open. No tests, builds,
probes, or Git operations were run for the textual proof repair.

## Independence, coverage, and failure conditions

There is no executable oracle, checker, seed, enumeration range, mutation
run, test, build, or frozen Oracle execution in this lane. Symbolic coverage
is all regular trees over the declared signature, all targets U in that D,
one isolated incoming binder row, and the specified extra-bound separator.
This is a candidate theorem, not bounded experimental characterization.
No model-search attempts or equivalent toy-probe variants were made.

The production graph is inherited from the reviewed static reduction;
its owner paths and tests were not re-audited here. The candidate order is
defined independently of production traversal, but both this note and the
prior bridge share the explicit variance/valuation interpretation. That
shared interpretation is exactly why this calculation cannot independently
validate source rules or solver denotation. The two prior input notes'
review sections do not count as independent review of this new artifact.

Symbolic discriminators address dropping an extra hidden upper, forcing a
cyclic lower to be equality, and reusing independently quantified witnesses.
They were not executed as mutations. The graph-to-fiber identity fails if
polarities or repeated binder occurrences do not share a value, if terms
have other meanings, or if hidden obligations are omitted. The projection
theorem relies on this candidate's structural order and regular Omega;
it is not a theorem under arbitrary H1–H2 carriers. The structural relation
cannot be extended to general concrete compatibility by transitive closure.

Omitted scope includes effects beyond the matched fixed pure leaves,
Union/Intersection, records, roles, outer/free anchors, source Apply,
general SCCs, production solver realization, diagnostics and resource
failures, principal residuals, runtime observations, and final Oracle
acceptance. No intended language meaning is reselected.

Recommended next action: obtain a focused independent review of this frozen
carrier/fiber derivation, then require an explicit bidirectional realization
map for the exact admitted target/session envelope before using it to close
H4. More finite pure-tree comparisons would not supply that map.

## Frozen inputs, checks, and resources

Direct input SHA-256 hashes:

```text
ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd  rules/research-lab.md
9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29  rules/design-authority.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e  rules/git-concurrency.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed  notes/design/2026-09-29-scc-intrusion-redesign-charter.md
beb998aabe285ed026a04cddb90055a6ea579c463457a4f1639e1e6ffc019a73  notes/progress/2026-09-30-intrusion-pure-source-typing-rules.md
fea42929e591c160d8a92edcb4f103254fb2726feef0be58ca747fb7075cf84e  notes/progress/2026-10-06-rec-name-return-member-scheme-bridge.md
f4ee1f71bea24c1150c90a274b41bc8fb9f8c2059c797c500a245fd4003f9779  notes/progress/2026-10-06-rec-name-return-purefun-production-reduction.md
```

Checks: static `cat`/bounded `sed` reads of named inputs; locator/context
`rg`; `sha256sum` for the seven direct inputs, rechecked at submission.
Large initial combined captures were truncated; narrow separate reads
supplied the governing fragments and complete two bridge notes. No complete
audit of every charter amendment, shared task record, or compiler file is
claimed. No Git command was used; the baseline is primary-supplied, and the
primary must compare these file hashes against it before integration.

Resource budget: symbolic derivation and static reads only, one leased note,
zero semantic executable probes, tests/builds/heavy processes, no scratch
outputs, no children or Git operations. At most four lightweight read commands
were launched together. CPU time, peak memory and total wall time were not
instrumented; no numerical resource cap was supplied. No search or process
was left running. Dependency stability is the hash snapshot, not a claim
that unrelated branch movement was inspected.

## Commit packet

* Exact leased path:
  `notes/progress/2026-10-06-rec-name-return-one-row-candidate-model.md`.
* Baseline SHA: `1e49e88f07fa8ceb0b05d109bab6c6a1f23d8d87`, supplied by primary.
* Changed dependency hashes: none during this lane; the seven hashes above
  pin the read snapshot. Baseline equality remains primary verification.
* Claim/review status: independently reviewed research-only regular-tree
  candidate model, carrier-law derivation, exact one-row fiber calculation,
  and symbolic extra-bound separator; no production denotation. The reviewed
  Spine-lemma repair is recorded above.
* Checks already run: static input reads and seven dependency hashes; no
  tests, builds, executable probes or semantic searches.
* Proposed one-line research-checkpoint commit message:
  `research: construct candidate fiber for one recursive member-use row`.
* Shared-record deltas intentionally left for primary/curator: record the
  candidate existence result, `P(U) iff Omega<=U` within this carrier, the
  one-added-upper separator, and the remaining bidirectional target/session
  realization obligation. Keep H4 conditional and denotation unselected;
  no shared task/index/authority/theory/question record was changed.

The bounded mathematical artifact and its reviewed proof repair are complete.
Any semantic expansion requires a new lease; solver realization remains open.
