# Callback coverage and source-preserving composition

Date: 2026-10-05
Status: Reviewed limited mathematical theorems; full main gates remain open
Scope: experiment-guided closure of the linked callback hiding step and
source-level obstructions to marginal common-allowance constructions
Approved-by: no new semantic or representation decision
Reviewed-by: independent compiler_referee and spec_auditor, 2026-10-05;
both found no blocking, major or minor findings in the proof/checker submission
Implementation authority: isolated research checker only; no compiler changes
Classification: C for the remaining production callback and principal gates;
the normalized pure structural FMP theorem remains A

## 1. What this attack establishes

The [scoped-lift experiment](../progress/2026-10-05-callback-scoped-lift-playground.md)
and [admission-hiding experiment](../progress/2026-10-05-callback-admission-hiding-playground.md)
separate two operations that must not be conflated: eliminating newly added
total definitions and forgetting old shared witnesses. This note proves:

1. Total definitions can be eliminated at their original scopes without an
   admission-uniformity premise. The original witness strategies and admission
   certificates survive.
2. The specified linked source/reference callback bounds are **equal**, not
   merely included, on every checked-admitted complete fiber.
3. After a legal existential marginalization of old witnesses, the comparison
   for that exact linked pair holds **if and only if** every actual complete
   observation has a checked-admitted representative. Section 4 gives the
   exact quantifiers. Uniform admission is sufficient but stronger.
4. A finite conservative dependency closure derives safe hiding for its
   eligible complement from the source rules. It includes proofs that a
   request or returned provider was actually produced in the retained history.
5. Composition through original source witnesses is compatible with the
   approved whole-observation projection without assuming that projection
   commutes with bind. A source-core `higher` instance defeats independent
   stage marginals; a supplied scalar selector defeats local representative
   substitution even when authority is retained.

These results do not choose the denotation of an arbitrary production effect
component, prove that a demanded common descriptor exists, or supply missing
direct-query resolution evidence. Section 8 states those remaining obligations
without weakening their quantifiers. The source examples refute specific
proof routes; neither is a counterexample to structural FMP or to every
possible principal common allowance.

The governing inputs are [Theorem C](2026-10-04-source-generated-callback-structural-theorems.md)
§§2–4, [source-indexed realization](2026-10-04-source-indexed-callback-realization.md)
§§2–5, [certified transport](2026-10-04-certified-callback-and-constrained-use.md)
§§2–6, [component linking](2026-10-02-parametric-component-linking.md) §§2–3,
the [approved observation decision](../../questions/2026-10-04-function-bound-value-observation/approved-answer.md),
and the [principal criteria](../progress/2026-10-04-principal-scheme-acceptance-criteria.md).
Only the existing finite decorated immutable source envelope is used. Its
primitive/provider relations and source/path/owner evidence remain independently
supplied valid inputs. No State or handler-image closure is inferred here.

## 2. Eliminating total definitions preserves scopes and admission

Let `E` be an original source relation presentation with its full binder tree.
Form `E+` by copying its whole old tuple and adding only fresh outputs defined
by total functions, exactly as in Theorem C §2.6. Each definition is placed
where all its operands are in scope. A shared derived coordinate has one
definition and one shared value; copying a child never rebinds an old shared
coordinate. There are no additional predicates on old operands and no extra
root alternatives.

**Theorem 1 (functional elimination).** Forgetting these fresh outputs gives
the original relation, its finite observations and its independently generated
admission relation, at the original scopes. Every old witness has a canonical
extension. This also holds for witnesses with the original rigid quantifier
dependencies. It needs no assumption that admission is uniform over arbitrary
values of the new outputs.

**Proof.** Evaluate the fresh definitions on the old well-formed tuple.
Totality and scope legality supply all new values without restricting that
tuple or consulting a later universal choice. At a parent, use the already
extended children with their same shared old operands, then evaluate its new
definitions. At a recursive source label, perform this construction along the
chosen finite derivation. Thus every finite witness has an extension `ext(w)`
with

```text
forget(ext(w)) = w
Obs(ext(w)) = Obs(w).
```

Conversely, a witness of `E+` satisfies every copied old premise; forgetting
the defining outputs gives an `E` witness. Their values on that witness are
forced by the definitions. This is a retraction, and a bijection on the
determined fresh values. It need not identify irrelevant choices at unreachable
branches of a proof strategy.

The same construction applies at every node of the original binder tree.
For example,

```text
exists s. forall kappa. exists z. R(s,kappa,z)

exists s. forall kappa. exists z,w.
    R(s,kappa,z) and w = t(s,kappa,z)
```

have corresponding witnesses `s,z(kappa)` and
`s,z(kappa),w(kappa)=t(s,kappa,z(kappa))`. This proof neither moves `s` inside
the universal nor hoists `z` or `w` outside it. The construction is logical
witness extension; it adds no source existential type or new solver operation.

Apply the same extension/forgetting to each finite admission certificate.
Every original source/provider/path/owner premise is copied, and a displayed
derived operand denotes its defining old expression. The original certificate
therefore remains valid in both directions. In particular, deleting the new
name is substitution of its total definition, not choosing a different old
carrier, request, returned provider or profile. Initial, response, resumption
and future-use certificates retain their original premises. No step assumes
the pending Function query. QED.

This theorem concerns an endpoint and its own definitional extension. It does
not equate actual and checked admission: the linked checked inlet still has
its original additional `d` constraints. Nor does it license removal of an
old witness that determines those constraints. A syntactic dependency scan
can see a new derived name in admission; inlining that name by this theorem
is sufficient, without demanding uniformity across its impossible alternative
values.

The scoped-lift checker independently tested 65,536 finite relation/function
pairs and 131,072 fixed-capture comparisons. Its capture-freshening,
body-hoisting and derived-output-hoisting mutants each have a two-row failure.
Those failures concern quantifier changes excluded by this proof, not the
legality of fresh total definitions.

## 3. The linked bound is exact on checked fibers

Fix the complete old fiber, original occurrences and a checked-admitted
challenge `h`. Write `A` for the actual source presentation and `C` for its
specified linked lift. The exact source/reference equation is

```text
F_C(X,Z,W) = F_A(X,Z) and Def_T(W;X,Z),     on a common admitted challenge.
```

The old argument-profile and body/result constraints are already present on
this common domain. Externally fixed `b,c,d` are not new outputs. The equation
contains all root alternatives of the specified presentation.

**Theorem 2 (common-domain equality).** At the common complete observation
boundary,

```text
P_C(h;xi) = P_A(h;xi)                      for h in D_C(xi).
```

The same equality holds after applying the same approved whole-observation
`Pi_xi` to both sides.

**Proof.** Extend an arbitrary actual derivation by Theorem 1 to obtain a
checked derivation with the same observation. Conversely, forget the fresh
outputs of an arbitrary checked derivation. Exact rule coverage gives an
actual derivation and the same observation. Both operations keep the complete
old tuple, binder tree and all finite future/resumption witnesses. Taking
their images under the same `Pi_xi` preserves equality. QED.

This strengthens the inclusion previously needed for Theorem C. It is not an
equality of domains, an equality outside `D_C`, an equation between independently
interpreted scalar effect rows, or a statement about an independently supplied
checked bound with unrelated conservative extras. Certified presentations
inherit it only through the corresponding complete transport certificate.

## 4. Exact old-witness coverage, and its quantifiers

### 4.1 Legal marginal setup

Let `x` contain the retained coordinates, and let `z` range over permitted
completions of the old witness at an eligible existential scope. For each such
completion there are actual and checked contracts `A_z,C_z`, satisfying

```text
D_C,z subset D_A,z
P_C,z(h) = P_A,z(h)                       for h in D_C,z.
```

All bounds below live in one complete observation space. Use the approved
projection once on each joined observation, with the declared common typed
transport if a legal hiding varies some old assignments. One may instead fix
the entire `nu,K,D` and vary only eligible remaining proof witnesses. In
neither case are two different values assigned to one retained coordinate.
The retained challenge is the same `h`, not just another challenge with the
same value types.

Define domain-qualified existential marginals:

```text
D_A^exists = union_z D_A,z
D_C^exists = union_z D_C,z

A_all(h) = union_{z: h in D_A,z} P_A,z(h)
A_checked(h) = union_{z: h in D_C,z} P_A,z(h)
C_all(h) = union_{z: h in D_C,z} P_C,z(h).
```

An inactive bound outside its own admitted domain contributes nothing. The
construction assumes that these are the marginals denoted by the legal hiding
at issue. It is not permission to move an existential through a rigid
universal. Where `z` denotes a scoped strategy, it is one whole strategy with
the original shared choices. In particular this pointwise contract theorem
does not establish a separately required `exists z. forall h` witness from
`forall h. exists z`; such requirements stay in the original binder tree.

### 4.2 Necessary and sufficient law

**Theorem 3 (coverage).** The existentially marginalized linked comparison
holds exactly when

```text
for every h in D_C^exists:
    A_all(h) = A_checked(h).                         (Coverage)
```

Equivalently, for each such `h`, every actual-admitted witness and each of
its complete observations has some checked-admitted witness with that same
complete observation:

```text
forall z, O.
  h in D_A,z and O in P_A,z(h)
  implies exists zc. h in D_C,zc and O in P_A,zc(h).
```

The representative `zc` may depend on the complete observation and retained
challenge, subject to the original allowed scope. It cannot change a retained
source owner, request/continuation relationship, typed path or shared fiber.

**Proof.** Projected domain inclusion is automatic: keep the same checked
admission witness and apply `D_C,z subset D_A,z`. Theorem 2 gives
`C_all(h)=A_checked(h)`. Domain inclusion also gives
`A_checked(h) subset A_all(h)`. Thus the requested bound inclusion
`A_all(h) subset C_all(h)` is equivalent to equality of the two actual-bound
unions. This proves necessity and sufficiency for the specified pair. QED.

This is an exact reduction of this hiding step, not a claim that Coverage is
automatically source-derived for every admission-live old coordinate.

### 4.3 Strictly weaker than uniform admission

At an admitted marginal challenge, consider three conditions:

- **H:** checked admission is independent of `z`.
- **S:** each actual-admitted `z` producing an observation at `h` is itself
  checked-admitted.
- **Coverage:** those observations have checked-admitted representatives.

Then `H => S => Coverage`, with both implications strict. Let both actual
fibers admit `h`, let only `z1` be checked-admitted, and use exact checked
bounds on that fiber:

| Actual bound at `z0` | Actual bound at `z1` | Conclusion |
| --- | --- | --- |
| empty | `{o}` | S holds; H fails |
| `{o}` | `{o}` | Coverage holds; S fails |
| `{o}` | empty | Coverage and the marginalized comparison fail |

The last row is the admission-hiding experiment's minimum obstruction. The
second row explains why demanding uniformity was unnecessarily strong.
Approved erasure can also establish Coverage when two raw complete quiet
returns differ only by an integer value. It cannot identify distinct request
origins to establish it.

### 4.4 Arbitrary conservative checked bounds require a different statement

If the only premise is `P_A,z(h) subset P_C,z(h)` on `D_C,z`, Coverage remains
sufficient. It need not be necessary for one particular checked endpoint:
that endpoint can contain a matching extra observation.

There is an exact robust form. Fix `D_A,D_C,P_A`. Coverage holds if and only if
the marginalized comparison holds for **every** family of checked bounds
satisfying that pointwise inclusion. Sufficiency follows by transporting the
covered observation. For necessity choose the permitted minimal family
`P_C,z=P_A,z` on checked-admitted fibers; a Coverage failure then remains a
comparison failure. No change of the source package or challenge is made
while ranging over these abstract checked completions.

This universal-over-completions result is a relational theorem. It does not
assert that all such completions are production descriptors. For the actual
specified exact lift, Theorem 2 already supplies the stronger fixed-pair
necessity in §4.2.

## 5. Deriving safe old hiding from source incidence

Coverage has a sound finite sufficient test using the source presentation,
without adding a predicate to the solver. First inline the fresh definitions
from §2. On the existing finite source graph and binder/incidence tables,
compute a conservative dependency closure for checked admission.

Seed it with all operands of the four admission schemas:

1. Initial: whole-carrier result interface, checked profile, source path,
   lexical/provider roots, compatible owner/view context and live `nu,K,D`.
2. Response: the exposed request, original operation/rigid witness, declared
   response port, retained continuation and current configuration.
3. Resume: retained handle, its request association and reentry continuation.
4. Future use: the returned descriptor, source label/roots, original typed
   port, next independent provider/force certificate and current context.

Close under all operands of source/primitive/provider/path/owner predicates
used in those premises, lookup and capture references, their residual
constraints, recursive back references, and binder dependencies. In particular
include the premises proving **production and retention** of an exposed
request or returned provider in the same history. Following only the displayed
tuple fields is unsound. Use the complete declared operand interface of a
supplied primitive relation; an undeclared semantic dependency is not an
admissible input to this test.

The closure terminates because it marks incidences and schemas in the finite
graph, including back references, rather than enumerating histories. It can
conservatively mark the entire relevant graph; no completeness or nonempty
private complement is claimed.

**Theorem 4 (safe complement).** An old body-owned existential can be hidden
with admission invariance if its occurrences and aliases are outside this
closure, the hiding is legal at its original scope, and no occurrence shared
with a surviving context, view, provider or residual is independently rebound.

**Proof.** Fix the live operands and a finite checked-admission certificate.
Changing such a complement coordinate leaves the operands of every used
predicate unchanged. Reuse its local primitive/provider witness. Lookup and
capture retain the same roots. The same argument applies to the source
production/retention premises for exposed requests and returned descriptors.
Induct on the finite certificate and its finite production derivations;
recursive references only increase finite derivation depth. Thus the same
certificate works at each permitted assignment of the forgotten complement.
The original binder dependencies ensure its witnesses remain in scope.

Context-proof locals can be reused; they need not be the actual behavior's
private locals. A genuinely shared occurrence would be in the dependency
closure or be disallowed by the hiding condition. The construction therefore
does not silently separate a shared context/body witness. This proves H,
hence Coverage and the safe marginal comparison. QED.

Ordinary source locals already bound within a constructor remain hidden
there. Theorem 4 does not claim that every informally "private body proof"
is independent of admission: the Response and Future-use schemas require
proof of actual production. The initial checked `d` profile can likewise
depend on an old shared coordinate. Those live coordinates require retention
or a genuine Coverage proof; membership equality on common checked challenges
cannot be used to prove that an actual-only challenge is checked-admitted.

## 6. Whole-witness composition and two source obstructions

### 6.1 A compositional presentation does not need projection congruence

Associate each original source relation `F_e` with the displayed observation
`Pi_xi(Obs(w))`, while keeping the old shared witness interface and binder tree.
Parents compose the original interfaces before hiding or displaying them.
This is the existing `Rel_C` source-reference construction, not a replacement
operational semantics on projected data.

**Corollary 5 (witness composition).** For every source graph in the supplied
finite immutable envelope, this finite presentation has exactly the typed
image of its source bound and the same independent admission relation, for
all finite latent/future/resumption histories.

**Proof.** Leaves keep their whole local relations; name, lambda and reify
keep their lexical/source references. Bind at Return joins the original
value and current configuration. Bind at Request retains the same request,
operation witness and continuation, appending the suffix to that continuation.
Call uses the original producer and inert carrier, receipt, actual entry,
typed rebind, body and designated consumer. A future use follows the actually
returned source label with its original captured roots; a resumption follows
the retained request/handle. Forgetting the displayed observation gives an
original derivation. Adding its deterministic whole-observation image gives
the reverse direction. The induction is on finite derivations with the
original rigid scopes; registered recursive labels need no finite bound on
the number of histories. Admission uses the same source certificates. QED.

No equation `Pi(A;B)=Pi(A);Pi(B)` is used. Intensional finiteness means a finite
source graph and its designated projection view, with primitive/view input
sizes counted. It does not mean that arbitrary extensional observation
equivalence or complete Function inclusion is decidable.

### 6.2 Why local integer saturation cannot be generalized blindly

For this counterexample only, supply an independently valid immutable local
primitive relation

```text
select(0,L,R) = L
select(1,L,R) = R.
```

Such a supplied exact primitive is permitted by Theorem C's proof envelope;
no current production declaration or surface syntax for it is asserted.
Let `L,R` be two already existing source closures of the same Function type,
each issuing the same declared request but with distinct retained request
origins/continuations. Use exact local relations for this example, so these
providers add no unrelated conservative behavior. Both are valid in the same
compatible context; no new capability or handler is introduced. Consider the
source-core relation

```text
bind x = result(0);
call(select(x,L,R), inert_argument).
```

The original middle witness is `x=0`, so the only selected provider is `L`.
The approved projection may erase the integer's identity in the final
observation. If one instead saturates the child return locally with all
integer representatives and uses the new representative as the suffix
operand, `x=1` selects `R`. Its right-origin request survives the approved
projection and has no original witness for this source. Existing authority
retention does not repair the wrong middle operand.

The witness construction in §6.1 succeeds: it always joins on the original
`x=0`, even if the displayed numeral has been erased. This explains both the
bounded scalar saturation experiment's success on its restricted bodies and
the obstruction to using it as a general higher-order abstraction rule.

### 6.3 `higher`: a lossless join is a concrete additional obligation

Fix the original `nu,K,D`. In the source-core specialization

```text
higher f g x = f g x
f y = y
x = Unit,
```

use Value entry, exact local relations and two same-typed source providers
`g_L,g_R`. Both emit a declared request `q`, at their respective source origins `L,R`, with
their own retained continuations and no consuming ambient handler. Let
`h_L,h_R` be separately admitted challenges supplying those providers. The
name, result, entry/rebind and future invocation rules give the selected
finite requesting histories

```text
(h_L, returned_provider=L, later_request_origin=L)
(h_R, returned_provider=R, later_request_origin=R).
```

At fixed `h_L`, the second-stage callee is the descriptor actually returned
by `f`, hence `g_L`. An independently reconstructed first-stage quiet marginal
and second-stage request marginal can instead admit
`(h_L,later_request_origin=R)`. No original source derivation produces it.
This argument observes the later request's origin at a fixed challenge; it
does not assume that an inert callable's data identity is publicly observable.

The exact algebraic test is useful beyond this example. For a complete joint
source relation `T` in a fixed ambient tuple space and proposed projections
`p_j`, define their natural reconstruction by

```text
J(T) = intersection_j p_j^(-1)(p_j(T)).
```

Always `T subset J(T)`. Reconstruction preserves complete witnesses exactly
iff `J(T)=T`. At the approved observation boundary its exact requirement is

```text
(id_challenge x Pi)(J(T)) = (id_challenge x Pi)(T).       (LJ_Pi)
```

**Proof.** A tuple belongs to `J(T)` precisely when each projected component
has some original witness, potentially a different witness for every
component. Exact reconstruction requires one jointly compatible source
witness for every such tuple. Applying the whole observation map gives the
second equivalence. The challenge coordinate is not erased. QED.

In the two-row example, projections retaining only challenge and later
observation give the spurious cross pair. Keeping the original returned
provider as the shared join coordinate repairs this example:
`(challenge,provider)` joins with `(provider,later_observation)`. These are
existing typed source incidences, not occurrence-specific selectors.
There is no assertion that this one join key suffices for every source graph;
other captures, residuals and history coordinates must also remain joint.

The later [source factor-cover theorem](2026-10-05-source-factor-cover-and-query-preservation.md)
supplies a finite sufficient test: each original relation factor has its whole
operand interface in a retained bag. It is sharp for guarantees uniform over
independently arbitrary factors on nontrivial product domains. Exact equality
then preserves every unchanged client and actual query/evidence relation.
Its fixed parity/provider source-core example defeats all proper projections
of one ternary dependency; retaining only pairwise overlap is insufficient.

This refutes independent marginal reconstruction, not a common descriptor
that retains and actually consults the original joint relation. Storing
`K_G` beside an export is not enough if that export's interpretation ignores
the retained provider incidence. Nor is an arbitrary complete relation
automatically an expressible public effect descriptor.

### 6.4 Sequential support is not an executed-prefix union

The same source equations give a direct guard on `compose` and `twice`.
With a Value-entry call, a suffix body begins only after the original Force
returns at its typed rebind path and current configuration. Induction over
Return/Request bind proves that a pending argument request retains the body
as its continuation suffix; it does not execute that body early.

For example, if `g` first requests Read and `f`'s body later requests Write,
the first pending Read prefix has no already executed body Write. After the
original continuation returns, Write may occur. Canonical may-support
`{Read,Write}` is consistent with this fact. Reconstructing complete observations
by an unguarded union of executed stage behaviors is not. Both `twice` uses
similarly retain their order, and `higher` additionally retains the returned
callee. These source guards coexist with `compose`'s hygiene-preserved outward
`g` contribution; they justify no new subtraction or concrete comparison.

## 7. Bounded checker and relation to earlier experiments

[`research_callback_admission_coverage.py`](../../tools/research_callback_admission_coverage.py)
tests the two-witness, one-challenge, two-observation universe. Its 4,096
encodings include inactive bound bits, so the counts are not counts of
distinct semantic contracts.

| Check | Exhaustive result |
| --- | --- |
| Pointwise domain/inclusion premises | 1,681 encodings |
| Exact linked bounds on checked fibers | 1,296; Coverage iff marginal comparison in all |
| Uniform checked admission | 1,105; all satisfy S and Coverage |
| Same-witness admission S | 1,465; all satisfy Coverage |
| Coverage | 1,521; all preserve the marginal comparison |
| Marginal comparison for the selected conservative endpoint | 1,593 |
| Fixed actual/domain families versus every conservative checked completion | 144; universal preservation iff Coverage |

The checker finds minimum examples separating H, S and Coverage, and a
particular conservative completion where comparison succeeds without
Coverage. The minimum exact-lift failure has three active domain memberships
and one active observation, matching the earlier one-observation obstruction.
An inactive-actual-bound mutant demonstrates why domain qualification is
necessary. A separate quiet-integer image example shows that approved final
erasure can establish Coverage without S.

The unbounded results are the proofs above, not an extrapolation from these
counts. This checker does not generate production endpoints, implement a
Function resolver, or decide source admission. Existing experiments were
read as scoped evidence: the scoped/hiding checkers motivate §§2–5; scalar
saturation and callable projection motivate §6.1–6.2; contract joins and
compose hygiene motivate §6.3–6.4. The concurrent
[Function-shadow checker](../progress/2026-10-05-function-shadow-obstruction-playground.md)
also preserves the already reviewed entry-path obstruction to importing pure
structural comparison into complete Function semantics. No broad compiler
tests are relevant to this isolated proof slice.

## 8. Remaining gates with their original quantifiers

### Callback production bridge

For the specified source-reference construction, complete witness realization,
definitional elimination and equality on the checked domain are proved.
Certified transformations preserve that result. A legal old-witness marginal
of this exact pair preserves the comparison iff Coverage holds; the source
dependency complement is a derived sufficient class.

The remaining production assertion must still account for **every** endpoint
membership and independent admission certificate of the actual production
presentation. An unexplained root alternative has no source witness by fiat.
If that presentation additionally hides an admission-live old coordinate,
Coverage at its legal scope remains a substantive obligation. Neither matching
printed ports nor success of a bounded trace enumeration proves these facts.

### Principal common allowance

Keep the accepted totality condition unchanged:

```text
forall xi. forall s in S_xi. exists a. Q_xi(s,a).
```

Here `a` must be an existing, legal, source-expressible common descriptor whose
required invocations pass their direct **whole Function** comparisons. One
shared component cannot be replaced by unrelated occurrence-specific choices.
Sections 6.1 and 6.3 identify how to preserve the source relation during a
candidate construction: retain its joint witnesses or prove `LJ_Pi` for an
actual marginal reconstruction. They do not themselves construct every
required descriptor port or attachment.

All-view principality also remains

```text
forall independently valid finite V.
    exists a solution-preserving admissible use m_V.
```

The finite constrained use already constructed in the certified-use theorem
still yields the exact remaining extension entailment. For a replacement
export `B_common`, it uses

```text
C_V(v) implies exists s,a.
    K_G(s,v) and Q(s,a) and Direct(B_common(s,a), R_V(v)),
```

with all locals freshened/hidden at their original scopes and all shared
dependencies retained. It cannot replace that last query by one through the
hidden original root.

There are two distinct proof tasks even after source witness composition is
correct. First construct the one legal shared descriptor, retaining the
actual source/provider correlations. Then obtain the existing direct-query
evidence for every independently valid view through the designated export.
Equality of source domain/bound at every old assignment preserves semantic
containment compatibility with every supplied target, by substitution of
equals. It does not prove that the endpoint-dependent resolver recognizes
that compatibility or produces all required cast/adapter evidence. The
complete comparison law is sufficient, not a characterization of every
registered adaptation. No successes of concrete comparisons are composed.

Thus the new exact results close defined local mathematical obligations and
exclude two source-realizable shortcut routes. They do not prove the full
production bridge or principal common-allowance theorem, and do not exhibit
a counterexample to either unrestricted goal. No new carrier, type-system
rule, rejection condition, public observation choice or compiler path is
selected. The earlier structural classification A is unchanged.
