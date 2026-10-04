# Source factor coverage and preservation of complete uses

Date: 2026-10-05
Status: Reviewed limited mathematical theorems; full main gates remain open
Scope: finite source-relation decomposition, complete client/evidence preservation,
and a fixed source-core obstruction to all proper marginal reconstruction
Approved-by: no new semantic or representation decision
Reviewed-by: independent compiler_referee and spec_auditor, 2026-10-05;
both found no blocking, major or minor findings in the proof/checker submission
Implementation authority: isolated research checker only; no compiler changes
Classification: C for full production callback and principal common allowance;
the normalized pure structural FMP result remains A

## 1. Result and governing scope

The previous [source-join theorem](2026-10-05-callback-coverage-and-source-joins.md)
§6.3 reduced exact marginal reconstruction to `J(T)=T`, or equality after the
approved whole-observation projection. This note supplies a finite sufficient
test from the original factors. It is also necessary for a **uniform** guarantee
over independently arbitrary factors on nontrivial product domains. Necessity
is not claimed for each individual source relation or for projected equality.

The test closes a useful part of the principal-use problem: a certified exact
decomposition preserves every unchanged joint client constraint and every
existing direct-query evidence alternative, not only semantic containment.
A fixed XOR/returned-provider source-core instance shows that even retaining
all proper coordinate projections can violate observable reconstruction.

These results preserve the existing carrier. They do not turn an arbitrary
relation template into a legal effect-component substitution target. Section 7
locates that remaining formation/interpretation rule and the actual production
generalization boundary. The distinction matters: exact relation preservation
is now proved for this class, while descriptor construction remains open.

Governing inputs are [Theorem C](2026-10-04-source-generated-callback-structural-theorems.md)
§2, [certified transport and ordinary uses](2026-10-04-certified-callback-and-constrained-use.md)
§§2–6, [parametric linking](2026-10-02-parametric-component-linking.md) §§2–3,
[concrete compatibility](2026-10-03-concrete-compatibility-boundary.md),
[callback B](2026-10-03-callback-context-delivery.md) §2.1,
the [approved observation decision](../../questions/2026-10-04-function-bound-value-observation/approved-answer.md),
and the unchanged [principal criteria](../progress/2026-10-04-principal-scheme-acceptance-criteria.md).
Primitive/provider contracts and decorated paths remain independent inputs in
Theorem C's immutable source envelope. No State, handler-image closure, new
selector, new public refinement or new inference existential is introduced.

## 2. Factor coverage implies exact reconstruction

Fix one legal source scope and its original outer environment. Let `U` be a
finite set of existing logical coordinates and `Omega` their allowed complete
joint tuple space. `Omega` need not be an independent product: the old rigid
permissions, typed dependencies and ambient restrictions remain in force.
It is not manufactured by defining it to be the desired solution relation.

Suppose the original, independently specified relation has the presentation

```text
T = {x in Omega | for every i, A_i(x|E_i)}.                 (F)
```

Here `E_i subset U` is the entire operand interface of factor `A_i`. Treat an
opaque primitive, residual predicate, recursive application or compound
subformula as one factor with all its free operands. Fixed outer parameters
are the same in every comparison below. There are finitely many factors.

For proposed coordinate bags `B_j subset U`, write `p_j(x)=x|B_j`, and define

```text
J_B(T) = {x in Omega | for every j, p_j(x) in p_j(T)}.
Cover(E,B) iff for every i, some j satisfies E_i subset B_j.
```

This is a join of projections of the **same whole relation**. It is not a join
of independently widened stage relations. Empty intersections mean `Omega`.

**Theorem 1 (factor coverage).** If `Cover(E,B)`, then `J_B(T)=T`.

**Proof.** Every `x in T` witnesses every projection, so `T subset J_B(T)`.
Conversely take `x in J_B(T)`. For any factor `i`, choose a covering bag `j`.
Membership in its projection supplies some `y_i in T` with
`x|B_j=y_i|B_j`. Therefore `x|E_i=y_i|E_i`; since `A_i` depends only on that
interface, `A_i(x|E_i)` holds. This works for every `i`, hence (F) gives
`x in T`. Different factors may use different `y_i`: agreement on each whole
factor interface is exactly what makes this sound. QED.

The proof includes empty `T`, zero-arity factors and empty bags. With a false
zero-arity factor, coverage supplies at least one bag whose projection is
empty, so reconstruction stays empty. With no factors, `T=Omega` and equality
holds for every bag family, including the empty family.

### 2.1 Deriving the finite condition from a source presentation

The test requires only the factor/operand incidence, once presentation (F)
and the proposed marginal interpretation are supplied. A conservative finite
construction assigns each factor to a bag and retains every operand there,
closing the inventory under its original source dependencies. This may keep
most or all of the graph. It proves no optimality or size reduction.

The complete interfaces include source roots, captures, returned providers,
current configurations, requests, saved continuations and pending suffixes,
typed paths, owners, residual/evidence dependencies and the predicates that
justify production or retention. A shared old coordinate keeps one identity
across every incident bag. Names of the same printed type do not substitute
for these dependencies. Admission factors must also be included when the
claimed relation includes admission; otherwise Theorem 1 says nothing about it.

A source union must remain one factor with its full interface unless a
separate equivalence justifies a decomposition. Splitting alternatives and
forgetting their shared branch dependence is not covered. Likewise, retaining
only request classification without its production/control premises cannot
certify ordered continuation behavior. The
[consumer experiment](../progress/2026-10-05-callback-consumer-factorization-playground.md)
shows why: a consistently relabelled Force replay passes its incidence check
but fails its independent source-history check.

Factor coverage is a finite certificate for an existing logical equivalence,
within the checked-rewrite clause of certified transport §2. It does not add a
runtime field, solver predicate, language rejection condition, or descriptor
formation rule. A decomposition whose interfaces cannot be enlarged legally
does not acquire that permission from this theorem.

### 2.2 Scope, private witnesses and recursion

The theorem is pointwise in all original outer coordinates. It can be used
under their unchanged binder tree. It never exchanges `exists z. forall h`
with `forall h. exists z`; choosing a different projection witness in the
proof does not rebind an original shared source witness in the presentation.

For example, at one permitted existential scope, with `z_1,z_2` disjoint and
genuinely private, the ordinary logical equivalence is

```text
exists z_1,z_2. A(h,k,o_1,z_1) and B(k,o_2,z_2)
  iff (exists z_1. A(h,k,o_1,z_1))
      and (exists z_2. B(k,o_2,z_2)).
```

It leaves the original shared `k` in both factors. Privacy requires absence
from the other factor, the surrounding client, live admission and residual
dependencies, with no movement across a rigid binder. If one original shared
`z` instead satisfies `A(z) iff z=0` and `B(z) iff z=1`, the joint existential
is false while independently hiding the two copies yields true. This is an
invalid change of binding, not an exception to Theorem 1.

For positive recursive presentations, apply the theorem only as a pointwise
identity of the defining operator. If `F(R)` is the original simultaneous
operator on candidate predicate interpretations and the proposed operator is
`F'(R)=J_B(F(R))` with complete factor coverage for **every** candidate `R`,
then Theorem 1 gives `F'=F`. Their finite-derivation least relations therefore
coincide: the finite approximants coincide by induction, hence so do their
unions. Merely observing equality at one fixed point, or saturating separately
projected recursive relations and joining afterward, does not meet this premise.

## 3. The condition is sharp for uniform independent factors

**Theorem 2 (uniform characterization).** Let `U` be finite, and now assume
`Omega=product_{u in U} D_u`, with each coordinate domain nonempty and having
at least two elements. Fix the factor scopes `E_i` and bags `B_j`. Then

```text
for every independent choice of relations A_i on E_i,
    J_B({x | all A_i(x|E_i)}) = {x | all A_i(x|E_i)}
iff Cover(E,B).                                           (UC)
```

**Proof.** Coverage implies the left side by Theorem 1. Suppose coverage fails.
Choose an uncovered factor scope `E`. If `E` is nonempty, choose for each
`u in E` a surjection `b_u : D_u -> {0,1}`. Make this factor the relation

```text
sum_{u in E} b_u(x_u) = 0 modulo 2,
```

and make all other factors universal. The resulting `T` is nonempty and
proper. Every bag misses at least one coordinate of `E`. Any tuple on that
bag extends to `T`: choose the other missing coordinates arbitrarily, then
use the last missing bit to satisfy parity. Consequently every bag projection
is full and `J_B(T)=Omega`, contradicting exactness. If `E` is empty, being
uncovered means there are no bags at all. Make its zero-arity factor false;
then `T` is empty but the empty reconstruction is the nonempty `Omega`. This
again contradicts exactness. Thus the uniform guarantee implies coverage. QED.

The nontrivial-product premise belongs only to this sharpness theorem. It is
not asserted of production `nu,K,D` fibers. Singleton coordinates can make a
syntactically uncovered factor harmless; empty ambient domains make equality
vacuous. In a particular source, other factors or functional dependencies can
also make an uncovered decomposition exact. Further, approved observation
erasure may give `LJ_Pi` even when raw equality fails. Theorem 2 asserts none
of their converses. It states the best uniform guarantee available from these
declared operand scopes alone when the factors are otherwise independent.

## 4. Every unchanged client and direct-evidence relation is preserved

Let `T'=J_B(T)` be certified by Theorem 1. Let `H(x,v,e)` be **any** fixed
joint relation involving an independent client tuple `v`, the original tuple
`x`, and evidence choices `e`. It may include all client constraints, method
and adapter alternatives, residuals, and the actual ordinary Function query.
Both presentations must use the same designated exported root and operands.

**Theorem 3 (complete use preservation).**

```text
T'(x) and H(x,v,e) iff T(x) and H(x,v,e).
```

Consequently every legal projection of either side, with its original scope
tree, has the same solutions and retained evidence alternatives.

**Proof.** Substitute the pointwise identity `T'=T`. This is equality before
any client or evidence projection, so each original satisfying tuple is also
a satisfying tuple on the other side with identical `v,e`. Applying the same
permitted quantifiers/projection on both sides preserves the equality. QED.

For the [ordinary-use construction](2026-10-04-certified-callback-and-constrained-use.md)
§5, take `H` to include `C_V(v)` and the existing
`Direct(R(x),R_V(v);e)`, together with its real scope/dependency conditions.
The theorem is uniform in every finite independent `V`. It preserves all
successful uses and their existing evidence; no separate completeness theorem
for the resolver is needed **for this preservation**. The query is the same
whole Function query on both sides. No concrete successes are composed and
no effect-port subtyping is introduced.

This is a statement about solution/evidence relations, not a proof that an
arbitrary operational solver preserves search choices or termination after a
rewrite. Nor does it turn independent semantic validity of `V` into a first
successful direct query. It cannot replace `R_G` by `B_common` in an operand.
Those are separate obligations in §7.

Consistent freshening of an ordinary use preserves the finite coverage
certificate, since it renames all factors, coordinates and interfaces by the
same injective action fixing the imports. Any further supplied admissible
whole-presentation transport can act on the established equality under its
existing theorem. This does not assert that arbitrary grafting commutes with
separately recomputing projected marginals.

### 4.1 The A/B experiment has an unbounded scheduling lemma

Let `S_B(x,w)` be the independently generated **complete** B solution relation,
including all real method/adapter/residual/evidence choices `w`. If an early
predicate `F(x,w)` is independently proved entailed by `S_B`, then

```text
S_A = S_B and F = S_B.
```

Both inclusions follow immediately from retention and entailment. The result
holds for empty solution sets and arbitrary domains or witness alternatives.
It is a checked logical rewrite at the unchanged scopes. In particular,
unary domains obtained by projecting complete B solutions are entailed facts;
adding them while retaining B does not lose any complete witness.

The [A/B playground](../progress/2026-10-05-callback-ab-solution-equivalence-playground.md)
tests that special case with supplied relations and fabricated evidence tags.
Its projection computation uses the solved B relation as an oracle. The
unbounded lemma supplies no production algorithm for finding entailed early
facts and no source interpretation of those tags. Actual A still needs an
entailment certificate for its propagated predicates and retention of all B
alternatives and the final completed-interface query. Endpoint-only equality
does not license deleting witnesses after their existential projection.

## 5. A fixed source-core obstruction to every proper marginal

The parity factor used in Theorem 2 can affect retained source observations;
it is not confined to an erased numeric correlation. Use Theorem C's supplied
primitive envelope with two independently certified pure instructions:

- `XOR(a,b)` returns the ordinary Int value `a xor b` for inputs 0 or 1;
- `SELECT(c,L,R)` returns the existing source provider `L` for 0 and `R` for 1.

Their contracts are exact on the stated inputs. They introduce no new public
bit type or refinement and create no new callable, owner or authority. The
input values are two immutable roots of one admitted client challenge. Take
two compatible same-typed source providers: a later invocation
of `L` or `R` emits the same declared request `q` at its respective retained
source origin and continuation. No ambient handler consumes these requests.
These are independently supplied source contracts, not claims that current
production HIR contains XOR, SELECT or application lowering.

Fix the single source-core construction

```text
c := XOR(a,b)
f := SELECT(c,L,R)
return f
```

and a separate valid future client which invokes the descriptor actually
returned at its original typed port, with the original current configuration
and a common valid argument. All entry, receipt, provider and continuation
rules are unchanged. The source rule gives the four possible XOR tuples

```text
T = {000, 011, 101, 110}                 (coordinates a,b,c).
```

Every pair projection `ab`, `ac`, `bc` is full. Their join is all eight bit
tuples, including `001`. All singleton and empty projections are full too,
so retaining **every proper coordinate projection** still adds that tuple.
Keeping the original ternary factor repairs this example.

Form the marginal family across these four admitted challenges **before**
restricting both interpretations to the same challenge `h_00` with `a=b=0`.
At `h_00`, the source forces `c=0`, returns `L`, and the later call can produce
the selected `q` observation only at `L`. The reconstructed relation permits
`c=1`, returns `R`, and produces `q` at `R` instead. The selector and future-call
relations themselves remain exact; only the XOR relation was reconstructed.

Write the complete source composition as `T_source = T and H`, where `H`
retains the exact selector, future-call and remaining source rules. The
reconstructed composition is `T_rebuilt = J_B(T) and H`. The approved `Pi`
erases the numeric data, but retains the request origin and continuation/
authority incidence. Hence the right-origin observation at that same challenge
is outside `(id_challenge x Pi)(T_source)` and inside the image of `T_rebuilt`.
This refutes observation preservation for this local marginal replacement in
its source context. It does not claim that a projection of a larger joint
relation which already retains a copy of the full ternary dependency must fail.
If one first restricted `T` to `h_00` before forming its marginals, `c=0` would
remain fixed and this counterexample would not apply. The order is material.

This is one fixed source-core witness against the stated reconstruction route,
not a refutation of every common allowance. A common conservative descriptor
might intentionally include both behaviors; exact reflection, all-view
principality and descriptor legality require their own tests. The example
also does not refute FMP, change the allowed carrier, or establish a production
counterexample. In particular its quantifier is not the original fixed-package
failure over every finite monoid quotient.

## 6. Focused executable evidence

The isolated checker
[`research_source_factor_cover.py`](../../tools/research_source_factor_cover.py)
enumerates factors and coordinate families over three Boolean coordinates.
The reconstruction code uses independent projection/membership, not the
syntactic cover predicate as its oracle.

| Factor schema | Factor assignments | Uniformly exact families out of 256 |
| --- | ---: | ---: |
| One ternary factor | 256 | 128 |
| Two overlapping binary factors | 256 | 160 |
| Three unary factors | 64 | 218 |
| One zero-arity factor | 2 | 255 |
| No factors | 1 | 256 |

Across all **148,224** factor-assignment/family cases it checks `T subset J(T)`
and coverage implies equality. For each schema and each family it separately
aggregates equality over every independent factor assignment and verifies
Theorem 2's iff. Counts are factor assignments, not necessarily distinct
resulting relations. Empty factors, empty relations and the empty bag family
are included.

The checker searches all proper nonempty ternary relations whose three pair
images are full. The minimum has four tuples, with exactly two minimizers:
even and odd parity. It checks `001` as an added tuple, its later right-origin
request at `h_00`, and the independently hidden shared-witness mutation from
§2.2. The unbounded arguments are §§2–5, not extrapolations from these numbers.
The model constructs no production descriptor and validates no actual Function
resolver. Current HIR and tagged A/B experiments were read as scoped evidence;
this proof slice requires no broad compiler test run.

## 7. Exact remaining responsibilities

### 7.1 Production membership across generalization and fresh use

The [HIR-backed experiment](../progress/2026-10-05-source-indexed-function-realization-playground.md)
now follows actual `id`/`zero` roots, returned `id`, aliases and fresh named uses.
Its 96 returned-Function modules exercise parsing, HIR, collection, routing and
generalization. The separately modeled 1,314 outer/future histories retain
those source identities, but the invocation semantics remain test-supplied.
The independent reference/consumer models do not exhaust membership of an
actual production Function bound.

The relevant production path is now located at named owners:

| Boundary | Current owner and established fact | Remaining correspondence |
| --- | --- | --- |
| Resolved source to root fact | `emit_resolved_binding_name`, `emit_lambda`, `admit_lambda_fact` in `crates/yu-solver/src/lib.rs` retain named-use and lambda recipe information and emit a Function lower contribution. | A lower contribution does not enumerate all members of an interpreted complete root bound. |
| Root row to scheme | `component_generalization_draft` follows the definition's actual root row into the F5 generalizer. Its Function finalization emits the four type children, with empty argument effect and bottom result effect in that case. | This is current F5 evidence, not the successor's complete source-owned membership rule. |
| Scheme to fresh routed use | `instantiate_and_route_closed_inner` decodes a `ClosedValueScheme` predicate and routes the instantiated components. | A source-witness decoding/freshening law must cover every alternative admitted at the use and preserve the original sharing/scopes. |

The source/provenance information also remains in `ConstraintStore`. No claim
is made that information is irrecoverably lost or that a new carrier is needed.
Nor is F5 selected as the successor semantic target. The exact bridge still
needs independently stated membership/admission rules at these owner boundaries
and a certificate covering all their alternatives. Once a rule is a covered
factor decomposition, §§2–4 discharge its relation and unchanged-use transport.
An unexplained new membership alternative or an independently rebound witness
is not certified. Admission-live hiding remains subject to the reviewed
[Coverage law](2026-10-05-callback-coverage-and-source-joins.md) §§4–5.

### 7.2 Common component introduction, then the designated direct query

The narrow unprovided rule is described in concrete compatibility under
**"Candidate abstract component as a same-fiber view"**: the mapping of one abstract
component to a projection of the existing complete relation at a source typed
path, including its fiber, component combination and typed-path transport.
The candidate shape is recorded, but that source rule is explicitly open.

For a finite source presentation with repeated effect-component occurrences,
the missing construction must supply **one legal existing descriptor term**
as their substitution target and derive its complete interpretation at each
typed path. The original stage/value carriers can differ; in `higher`, the
first callee can receive a Function-valued argument while the returned callee
receives an Int-valued one. Keeping their source incidences is necessary, but
it neither equates the carriers nor supplies the single component term.

Freshening copies original identities. Factor coverage changes presentation
of the same relation. Scoped hiding eliminates eligible locals. Grafting
inserts a **supplied legal** descriptor. None of these operations independently
introduces that common substitution value. A semantic relation join or flat
support union likewise needs the existing descriptor formation/interpretation
rule before it can witness the required `a`. Section 5 blocks a marginal
shortcut; it does not prove that such a rule is impossible.

The totality claim therefore remains, with its exact original quantifiers,

```text
for every xi, for every s in S_xi, exists a. Q_xi(s,a).
```

Here `Q` requires the source-expressible, well-scoped common descriptor and
every required direct **whole Function** invocation comparison, preserving
all old dependencies. It is not defined by successful query execution.

All-view principality still requires

```text
for every independently valid finite public V,
    exists a solution-preserving admissible use m_V.
```

For the finite ordinary-use construction and actual replacement export, the
remaining entailment is precisely

```text
C_V(v) implies exists s,a.
    K_G(s,v) and Q(s,a) and Direct(B_common(s,a), R_V(v)),
```

with the original binder tree. Theorem 3 eliminates a separate query-
preservation concern for a certified rewrite of that **same** interpreted
export. It does not replace its final query by `Direct(R_G,R_V)`, infer it
from other concrete successes, or manufacture evidence from semantic validity.
For an actually retained export, the earlier retained-root corollary applies
on its stated premises; it does not reinterpret the accepted common schemes.

Thus this slice closes exact source-factor reconstruction, establishes its
sharp uniform boundary, preserves all unchanged client/evidence extensions,
and rejects a fixed observable marginal route. The full production and common-
allowance goals remain C. No genuine counterexample to either full goal has
been established, and no new implementation or representation choice is made.
