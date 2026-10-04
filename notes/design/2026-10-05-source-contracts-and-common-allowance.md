# Source contracts for Function realization and common allowances

Date: 2026-10-05
Status: Reviewed conditional mathematical package, including Option 2 extension; concrete clauses remain Draft
Implementation authority: none
Supersedes: none
Base inspected: `c5262911`; approved Option 2 integrated at `74eab866`, `research/simple-sub-intrusion`

## 1. Answer and limits

Additional source-generated hypotheses can make the next proof obligations
constructive. They cannot supply the meaning of an otherwise unspecified
complete Function bound or the missing evidence alternatives of an otherwise
unspecified resolver. This note therefore distinguishes three ingredients:

1. a local interpretation contract for **existing constrained presentations**;
2. finite source emission and transport certificates;
3. local whole-Function comparison certificates.

**Current policy:** the committed
[approved Function-bound answer](../../questions/2026-10-05-production-function-bound-membership/approved-answer.md)
selects **Option 2**. Production bounds may have conservative observations with
no source-constructor witness. Sections 2–3.6 construct and certify a source
base; they must not be imposed as a source-tight production membership policy.
Section 3.7 adds an exhaustive positive abstraction grammar, including
unanchored extras, and proves a corresponding conditional production bridge.
The concrete abstraction primitives and complete membership grammar remain
unselected, exactly as the approved answer requires.

Under the contracts below, this note proves:

- **C-realization:** exhaustive membership/admission correspondence for the
  source base, including certified generalization and use; **C-abstraction**
  transports the callback result through explicit conservative production
  abstraction without requiring final observations to be source-generated;
- **A-extension:** a legal common allowance for every original solution,
  with exact forgetful projection and no equality of original contributors;
- **A-allocation:** factorization through the actual common export for every
  independently valid finite view in the specified source-allocation
  abstraction, with the stated fixed non-coverage interface premises.

These are conditional theorems, not an unconditional closure of the current
production/principality gates. In particular, `A-allocation` does not quantify
over every exact-execution-valid contract, arbitrary adaptations, arbitrary
value-interface changes, or every completion of the currently open effect
semantics. Its view class is defined independently in §6. It is not defined as
the instances of the inferred common scheme.

The contracts are a candidate for completing currently open formation and
comparison clauses. They do not replace an already selected complete
descriptor interpretation, select a new type constructor/carrier, or authorize
a compiler rejection policy. A failed certificate is outside this conditional
theorem, not a reason to reject the source program.

### Governing sources

The construction uses the existing relation `Rel_C` and presentation fields
`V,M,Q,K,D` from the [coupled core](2026-10-01-coupled-effect-interface-core-draft.md),
the [source-generated theorem C](2026-10-04-source-generated-callback-structural-theorems.md),
the [reference realization](2026-10-04-source-indexed-callback-realization.md),
and [certified transport/use](2026-10-04-certified-callback-and-constrained-use.md).
The [typed core](2026-10-02-typed-computation-core-elaboration.md) §§6, 8–9
governs entry, fixed-domain guarantee weakening and complete comparison.
[Concrete compatibility](2026-10-03-concrete-compatibility-boundary.md) §1
governs flat positive components, whole Function queries and concrete-success
non-composition. The [charter](2026-09-29-scc-intrusion-redesign-charter.md) §9
permits a stated conservative effect abstraction; it does not select the
particular abstraction below.

The [latest complete-root audit](../progress/2026-10-05-source-indexed-function-realization-playground.md)
is respected: retained HIR/provenance and four Function children do not by
themselves decide exhaustive membership. The interpretation contract in §2 and
abstract rules in §3.7 are explicit additional hypotheses, not facts inferred
from that audit. The later approved answer supersedes treating source-tight
membership as the production target.

## 2. An independently interpreted constrained presentation

Fix the original binder tree and a fiber `xi = (nu,K,D)`. All statements below
are made at those original scopes. Metatheoretic local witnesses do not add
existential source types.

### 2.1 Generic relation clauses

Use a finite typed rule graph `E`, represented by the existing constrained
presentation and its source/operand references. Its clauses have the following
generic meanings, before a particular source translation is supplied:

| Clause | Interpretation |
| --- | --- |
| Primitive | The independently specified whole-tuple local relation. |
| Conjunction | Both predicates on the same shared tuple. |
| Union | One original whole-tuple alternative. |
| Renaming | One capture-avoiding action on all incident operands. |
| Scoped binding | The original logical binder at its original position. |
| Constructor image | The independently specified Return, Request, Bind, Call, closure, delay or consumer relation. |
| Recursive reference | Reference to the registered relation root. |
| Positive recursion | Least relations generated by finite derivations, including the specified finite-prefix rules. |

These are the existing relational operations of theorem C. `E` is proof
notation for a presentation, not a new runtime object or type constructor.
The input includes the independently typed primitive and owner/view kernel
contracts; no global Function-containment oracle is one of the clauses.
For production, `E` includes the explicit abstract rules of §3.7 as well as
its source base. An abstract rule need not be a source constructor.

### 2.2 Active constrained-root interpretation

The additional interpretation hypothesis is:

> Retained membership, admission and provider-contract clauses are semantically
> active at their recorded typed incidences. They are interpreted jointly with
> the ordinary descriptor, on the same whole provider/observation tuple and
> original binder environment.

Let `M_E` and `A_E` name the membership/admission predicates already presented
by that graph. These names introduce no additional semantic coordinate.
Schematically, the complete constrained root has

```text
D_E(xi) = { h | A_E(h;xi) },

P_E(h;xi) = { Pi_xi(O) |
    M_E(h,O,w;xi) and DescMem(R_E,O,w;xi)
    for a witness w at its original scope }.
```

`DescMem` is the existing, independently interpreted descriptor judgment.
It is not defined as the source image. A constructor typing lemma must prove
it for each emitted observation; without that lemma the descriptor conjunct
could discard generated witnesses.

Complete Function admission is evaluated in the retained constrained
interface, including its source-incidence predicates. The hypothesis does
**not** say that conjoining a predicate on an observed execution can discharge
a bare Function's obligation on a larger challenge domain. The admission
clauses themselves must explicitly contain the retained provider contracts.
Section 5 specifies those clauses for the common-allowance subcase.

If source links are only explanatory metadata, this hypothesis fails. If a
generalizer discards these predicates, it also fails. Neither failure is
repaired by correctly printing the four Function ports.

## 3. Finite source emission contract and C-realization

### 3.1 Source envelope

Use exactly theorem C's finite decorated immutable source graph:

```text
d = literal | name | lambda(P,c) | operation(decl) | reify(c)
c = result(d) | eliminate_p(d) | call(cf,ca) | bind(x,c1,c2).
```

Recursive references are monomorphic and preallocated. Immutable records,
captures and aliases retain their original provider roots. Each separately
supplied finite client/provider graph is checked by the same contract; there
is no bound on the number or length of its finite future interactions.

The source supplies actual roles, parameter entry, declared operations,
typed paths, owners, receipts, raw resumptions, result consumers and the
original shared tuple. There are no mutable cells, opaque uncertified imports,
implicit adapters, or offered handler-image nodes. Independently source-typed
ambient handler contexts may be present and remain the same on both sides.
These restrictions are theorem boundaries, not new source rejection rules.

### 3.2 Emission inventory

Every emitted root clause and every alternative is accounted for by this
inventory or a certified transformation. Every source constructor has its
required emitted clause.

| Source node | Required relation clause and incidence |
| --- | --- |
| Literal/primitive | Original whole-tuple local relation and declaration/contract identity. Conservative alternatives originate at that leaf. |
| Name | Original resolved lexical root, including its dependent provider roots. |
| Immutable record | Original field-provider tuple with its sharing; construction does not force latent fields. |
| Lambda | Inert closure; actual role, entry, body, consumer and captured roots. |
| Operation | Original declaration-instance map, native delimiter and declaration-derived consumer. |
| Reify | Inert delay at the original computation/provider root. |
| Result | Same returned descriptor/provider and current configuration. |
| Eliminate | Exactly the source-designated one-layer port and consumer. |
| Bind | Shared result/rebind/state witness and the original ordered suffix. |
| Call | Callee, inert whole argument, actual receiver/receipt, actual entry, body, designated consumer and invocation return. |

In particular,

```text
Return(v,C) >>= S = S(v,C)

Request(q,C,k) >>= S
  = Request(q,C, lambda(response,C'). k(response,C') >>= S).
```

Value entry is receipt, one designated argument Force, typed rebind, body,
consumer and return. Retained-computation entry binds the same carrier
without that entry Force. A resumed request retains its original witness and
continuation and uses the current resumed state. It does not replay receipt.

The source-base checker rejects an unexplained source rule in the **proof
artifact**. Production root alternatives may additionally use §3.7's declared
abstraction rules. Every alternative is accounted for, but its final
observation need not have a source-constructor derivation. Port compatibility
alone does not supply its typing/effect/authority/dependency certificate.

### 3.3 Independent admission and complete histories

The admission inventory is separate:

1. the source-typed initial punctured context, with original slot, provider,
   whole argument, result path and joint dependencies;
2. a typed response to an already exposed request, at the same operation
   witness and current configuration;
3. use of that request's original raw resumption handle;
4. a source-typed future call/force at an actually returned provider's original
   typed port.

No case asks whether the pending Function comparison succeeds. None derives
an argument-domain restriction from the spelling `never`. A divergent carrier
can be admitted without having a return observation. All finite prefixes,
future uses and resumption developments are included, not merely a bounded
test grammar.

### 3.4 Generalization and use

Each post-generation transformation supplies a finite certificate from the
already reviewed inventory: whole injective freshening, legal uniform graft,
locally proved equivalent rewrite, total fresh-coordinate definition,
original-scope joint hiding with its required admission certificate, and
unchanged client/direct-query conjunction. Rigid imports stay fixed; `K,D`
and all their incidence move together. A shared witness is never independently
hidden per segment. Certificates for arbitrary equivalence are not supplied
by an oracle.

For normative literal B, expected context supplies the known Handler boundary
before body generation; the parameter/body/result endpoints are independently
generated; the completed literal is tested by one ordinary inequality. This
proves the formation/correspondence of a B output, not success of an arbitrary
unrelated annotated literal.

### 3.5 Theorem C-realization

Assume §2, the local descriptor typing lemmas, and §§3.1–3.4's finite
conformance certificate for the **source base**. Then every membership/admission
derivation of that base translates to a source-generated derivation with the
same scopes and joint witness, and conversely. The correspondence survives
the certified generalization and fresh use. Consequently theorem C's linked
Pure-value lift gives complete callback containment at those base roots.
Full production root containment uses §3.7, rather than assuming no root extras.

**Proof.** Induct on a finite membership derivation. Exhaustive accounting
identifies its last rule with one source constructor or one certified
transformation. Translate its premises inductively. The constructor table
gives identical source operands, providers, state and binders. Its local typing
lemma supplies `DescMem`. At a primitive, use the same local relation witness,
including any independently certified conservative alternative. At a recursive
reference, a finite derivation uses only finitely many unfoldings. Reverse
induction on the source derivation gives the converse.

The four admission constructors give the corresponding independent induction
on admitted histories. Transport through a certificate follows the existing
renaming/graft/joint-hiding lemmas, at the original scopes. Apply the same
whole-observation `Pi` once. The resulting actual/checked roots meet theorem
C's hypotheses, so its lift containment applies. No concrete-success chain
or change of actual Pure/Handler role occurs. QED.

### 3.6 The check is finite before implementation exists

Index source/output nodes and binders; match constructor tags and ordered
operands; account for every output alternative; check explicit references and
scopes; check the admission inventory; check positive recursive blocks and
their finite-derivation convention; validate each transformation proof step;
check designated roots and the final projection.

For `n` source/output nodes, `i` explicit incidence entries and `t` explicit
certificate entries, these syntactic checks can be implemented in
`O(n+i+t)` with indexed identities, preprocessed scope ancestry and linear
graph traversals. This bound counts all supplied dependency/correspondence
data. It excludes proving a new primitive contract or arbitrary logical
equivalence, solving the original constraints, and computing principal types.
It is not a complexity claim about production inference.

This is a proof-before-code contract: a later implementation has a concrete
constructor-by-constructor conformance obligation. It need not first exist
before the conditional theorem can be proved.

### 3.7 Option 2: explicit positive production abstraction

The approved Option 2 permits conservative root alternatives. A useful
source-generated sufficient condition is that the actual/checked source bases
use **paired positive abstraction grammars**, with their invariant parameters
and complete constraints transported together. It is not necessary to decode
every final production observation into an actual source execution.

Work before `Pi`, on whole tuples at a fixed `xi,h` and original scope tree.
Write `R` for the source-base relation. Let `G` be the root's required complete
constraint envelope: ordinary descriptor membership, genuine guarantee bounds,
admission-dependent typed/provider conditions, original `K,D`, authority and
scope predicates. Source-base typing proves `R subset G`. `G` is not merely
a family-support filter and does not discard original bound equations.
The source execution derivation belongs to `R`; it is not itself required of
every member of `G`. This is the distinction selected by Option 2.

The following finite rule grammar is a concrete sufficient abstraction shape:

```text
H_G(R) = least X such that
  X(y) iff G(y) and (
      R(y)
      or Z(y)
      or exists x,z. X(x) and W(x,y,z)).
```

`W` and `Z` are independently interpreted **whole-tuple abstraction relations**
in the existing carrier. They do not test `Direct`, absence from `R`, a query's
success, or raw endpoint-ID equality. Their finite contracts identify fixed
and changed coordinates, all operands, original scopes and any introduced
provider/future-use rules. The original assignment and shared dependencies
remain attached; a new observation cannot acquire an unlicensed capture grant
or operation witness by matching a row family. The guard `G` checks all
required constraints at the final tuple, not only at a source anchor.

The `Z` arm admits independently licensed extras with **no source anchor at
all**. The `W` arm permits finite abstract rewrites of an existing tuple. Both
are exhaustive declared alternatives, not arbitrary port-compatible behavior.
These relations are not selected by this note; their validity/certification is
an explicit remaining primitive-design obligation. They can use the existing
finite positive relation clauses or independently certified local relations,
with their full interface counted in the checker. Their invariant parameters
are independent of any coverage coordinates being varied in the comparison;
coverage-dependent primitives need their own parameter-inclusion certificate.

The external source environment and original rigid assignments are parameters
of this grammar. Its recursion uses only finite-arity conjunction/union and
existential relational images in `X`. An infinite universal quantification
over `X` is not an abstraction-grammar constructor. Thus membership has a
finite derivation; a fixed universal source binder is checked pointwise at its
original position, not moved into the recursive operator.

**Extensivity.** If `R subset G`, every `R(y)` enters by the identity arm, so
`R subset H_G(R)`. Thus this is a conservative over-approximation of the source
base, even though abstract outputs need not be source executions.

**Two-parameter monotonicity.** Suppose

```text
R_A subset R_B,       G_A subset G_B,
```

with the same `W,Z`, whole parameter interface and original scopes. A finite
derivation under `R_A,G_A` is also a derivation under `R_B,G_B`: a source leaf
uses the first inclusion, a guard uses the second, a `Z` leaf is unchanged,
and an abstract step retains the same `W` witness and translated predecessor.
Induction on that finite derivation proves

```text
H_GA(R_A) subset H_GB(R_B).
```

This covers every unanchored extra and every finite chain of abstract steps.
It proves monotonicity from the grammar, without assuming production inclusion.

**C-abstraction theorem.** On each checked-admitted fiber, apply C-realization
and theorem C's total-coordinate identification to the linked actual and
checked source bases. A production pair is certified when:

1. both complete membership grammars are exactly the displayed abstraction
   construction over their respective bases, with no unaccounted alternatives;
2. `W,Z` and their parameters match under the original-tuple correspondence;
3. the hard envelopes are identical there, or have a finite clause proof
   `Le(G_A,G_C)` of §5.3; source typing proves `R_A subset G_A` and
   `R_C subset G_C`;
4. admission remains the independently source-generated domain of §3.3, and
   all future-use/admission rules of abstract providers are supplied in the
   same certified grammar with that same admitted domain. Positivity of
   membership does not prove this condition. An abstract rule that changes
   admission-live history/provider coordinates needs its own domain certificate
   and is outside the unchanged-domain subcase unless that certificate applies;
5. whole generalization/use transports the combined source, guard, abstract
   relations and primitive certificates uniformly.

The base inclusion and two-parameter monotonicity give

```text
H_GA(R_A) subset H_GC(R_C),
```

and applying the same `Pi` gives the full production callback containment.
Admission inclusion is the original independent theorem C clause; enlarging
membership does not infer a new challenge domain. If production also changes
admission, it needs a separate domain certificate and is outside this subcase.

Identical envelopes can be verified by finite schema/dependency matching,
rather than a global inclusion premise. A nonidentical envelope must have the
actual finite local proof; typing alone is insufficient. This is a conditional
production theorem for the linked template. An unrelated callback formal can
have a different abstractor and is not automatically covered.

**Transport and the common export.** Capture-avoiding freshening applies to
`W,Z,G` and every incident operand; they cannot branch on the spelling of the
submitted root. The finite checker verifies paired grammar and parameters,
positivity, primitive interface/certificate identity, hard constraint exposure,
complete alternative accounting and transport maps. Its syntactic cost includes
these nodes and all explicit certificate entries. For the common theorem,
equality from absorption remains equality under the same paired abstraction.
More generally §7's `Le` proofs for the base and hard envelope lift through the
displayed positive grammar by `Le-C` and finite recursive equation pairing.
The actual root query still names the common export.

**Why the hard guard matters.** Adding a constant `Write` extra to a provider
whose retained bound is fixed to `Read` would violate that original solution.
A typing-only or authority-only guard would miss this. The complete `G`
retains the declared guarantee and excludes that extra. Conversely a permitted
extra satisfying `G` can be admitted even if absent from `R`.

For a finite algebra illustration, take distinct admissible whole tuples
`x,y`, a complete envelope `G={x,y}`, source base `R={x}`, extras `Z={y}` and
no rewrite edges. Then `H_G(R)={x,y}`. Tuple `y` has no source-base membership
witness. This illustrates Option 2's policy; it is not a claimed Yulang source
realization or a specification of an actual abstract request/provider rule.

The construction is a sufficient **shape for an exhaustive membership
grammar**, not proof that current F5 already has it or that arbitrary safe
abstractions admit these finite certificates.

## 4. Genuine provider bounds, not exact-trace filtering

The common-allowance theorem needs a more specific component interpretation.
Fix a complete non-coverage envelope `N_j` for an original typed provider port.
It contains the actual role, entry, full challenge/future-response domain,
value paths, operation-instance predicates, continuation/provider relation,
routing conditions and all original shared dependencies.

Let `u` be a **whole provider witness**. Define `Bound_j(E,u;xi)` by:

1. `u` satisfies `N_j` on all its admitted finite interactions;
2. every genuine guaranteed may-bound observation at the selected output
   fields is covered by `E`, under the same assignment and dependencies.

The may-bound is part of the provider interface. It may conservatively admit
requests that no particular execution makes. It is not obtained by collecting
the requests in one execution of the surrounding source program. Returned
providers and all finite future uses are covered by the same predicate.

Changing `E` in this definition changes only guarantee upper bounds. It does
not change the provider's challenge domain, capture contract, role, or future
argument interfaces. If a component controls any such field, it is not an
eligible occurrence for this lemma. The finite A/G inventory of typed core §8
is used at the **provider being compared**, not as permission to change an
arbitrary field below its parent's input.

Interpret legal positive flat components at one joint assignment by

```text
Allow(flat{E1,...,En},xi,q) = or_i Allow(Ei,xi,q).
```

Occurrence identity and all constraints remain in the residual. Every input
row fiber must be jointly well formed/nonempty in the existing typed-row
sense. An empty request support is allowed; inconsistent binder predicates
are not converted into empty support and accepted vacuously.

### Lemma 1: provider-bound monotonicity

If `Allow(E,xi,-)` implies `Allow(A,xi,-)`, then

```text
Bound_j(E,u;xi) implies Bound_j(A,u;xi)
```

for every whole `u` at the original binder scopes.

**Proof.** Retain `N_j`, all challenges and the original provider witness.
For every admitted finite interaction and every guaranteed may-bound point,
the old coverage implication followed by the displayed set implication gives
the new coverage. Every non-coverage predicate is identical. This is direct
universal reasoning about one provider; it is not transitivity of concrete
Function successes. QED.

### Lemma 2: active same-provider absorption

Under the same implication,

```text
Bound_j(E,u;xi) and Bound_j(A,u;xi)
    iff Bound_j(E,u;xi).
```

The right-to-left direction is lemma 1; the converse drops a conjunct. The
same `u` and original scope are essential. Independent provider witnesses
would give a different formula. Arbitrary other predicates `Phi` may be
conjoined to both sides, including correlations between different providers.

These lemmas are valid for conservative complete provider bounds, unlike the
shortcut `exact source image and coverage(A)`. They also do not prove
monotonicity when widening `A` changes an admitted input domain.

## 5. Common formation and A-extension

### 5.1 Explicit local formation conditions

The generator supplies a finite inventory of selected guarantee occurrences
`j`, their original descriptor terms `E_j`, and the outer guarantee `E_out`.
The following are additional, locally checkable formation conditions:

- **Scope:** every constituent is a legal existing positive component at the
  common binder scope. All free identities, including hidden dependency
  references, remain available at every selected occurrence. No arm-local
  rigid binder is exported by flattening. Recursive terms remain references.
- **Variance:** within each compared provider, selected fields are genuine
  guarantees; its challenges, future argument fields and invariants are fixed.
- **Incidence:** old `Bound_j(E_j,u_j)` and the common occurrence
  `Bound_j(a,u_j)` constrain the same original whole provider `u_j` in the
  parent admission clause. Corresponding old output predicates remain at the
  same whole observation in the guarantee clause.
- **Retention:** all original constraints, endpoints, roles, sharing, `nu,K,D`,
  value comparisons and evidence remain conjunctively present.

The incidence condition is semantic as well as structural: the active
constrained-root interpretation in §2 must interpret the references that way.
A retained but inert provenance edge does not satisfy it.
For each changed selected descriptor occurrence, its **ordinary `DescMem`
clauses themselves** must expose exactly the fixed non-coverage predicates and
the eligible `Bound` guarantee leaves used here, at the original scopes.
Keeping an old descriptor predicate does not make a changed one identical.
A descriptor whose actual membership lacks this decomposition is outside this
sufficient formation class; no unexplained descriptor conjunct is erased.

For a fixed old solution `s`, the relevant clauses have the form

```text
D_old(s,h) = N_D(s,h) and Phi_D(s,h)
             and all_j Bound_j(E_j(s),u_j(h);xi),

D_common(s,a,h) = D_old(s,h)
                  and all_j Bound_j(a,u_j(h);xi).
```

The guarantee clause has the same shape: retain the old whole observation
predicate and its original bounds; conjoin the common guarantee views at
their original typed output incidences. The common root is the actual
ordinary descriptor designated for export. Its complete interpretation is
this retained constrained presentation; its bare printed ports do not erase
the residual.

This does not assert that a fixed old solution acquires a larger domain.
Complete-domain equality after absorption is intentional. The generalized
family retains all old solutions, rather than forcing one old solution to
handle every other solution's providers.

### 5.2 Construct the common term

For each old solution, choose the existing finite descriptor term

```text
a_s = flat{E_out(s), E_1(s), ..., E_n(s)}.
```

The syntax template is fixed by the source inventory; it is not selected by
successful queries. Its interpretation at `s` is the same-fiber union. The
scope condition makes it legal without a new tuple-valued effect component.
It contains every old selected allowance; they need not equal one another.
The presentation does not impose the equation `a = a_s`. The fresh common
coordinate remains constrained by the required complete views; `a_s` is one
constructive totality witness. A wider independently legal allowance may also
satisfy those constraints.

### 5.3 Local complete-query certificate

Here is a restricted finite certificate calculus sufficient for this note.
It is proof syntax checked inside the one ordinary Function query, not a
second source inequality or new solver carrier. It is intentionally incomplete
for arbitrary concrete comparisons.

`Gamma` is the original scoped predicate environment, including the supplied
source allocation certificate. `Eq_Gamma(F,G)` and `Le_Gamma(F,G)` are proof
judgments about the explicitly presented joint relation clauses. They are
not calls to an extensional relation-inclusion oracle.

**Coverage proofs.** `Cov_Gamma(E,A)` proves the pointwise implication between
the two allowance predicates. Its finite DAG uses identity, injection into an
existing flat union, disjunction elimination, or a referenced scoped coverage
clause of `Gamma`. A reference must identify that very original predicate and
all its dependency operands. Logical implication may compose within this DAG;
successful concrete Function queries may not. The certificate is checked
relative to `Gamma`; solving an arbitrary residual clause is not hidden in
this checker.

**Provider leaves.** For exactly the same whole provider operand and the
same fixed non-coverage envelope, the rules are

```text
Cov_Gamma(E,A)
----------------------------------------------------------  Guarantee
Le_Gamma(Bound_j(E,u), Bound_j(A,u))

Cov_Gamma(E,A)
----------------------------------------------------------  Absorb
Eq_Gamma(Bound_j(E,u) and Bound_j(A,u), Bound_j(E,u)).
```

The checker verifies the complete A/G inventory and every operand of `N_j`;
future input domains and invariant fields cannot change. The two rules are
lemmas 1–2. All other primitive or descriptor predicates have an `Eq` leaf
only when their original relation identifier, typed operands and scope agree
under one supplied legal renaming/graft. Existing value/structural constraints
are retained; the calculus does not infer a new value conversion from matching
effect support.

**Constructor congruence.** Identity and symmetry/transitivity of `Eq`, and
use of `Eq` in either direction as `Le`, are ordinary logical proof rules.
For each fixed positive relation constructor `C` of §2.1:

```text
Eq_Gamma(F_i,G_i) for every child i
----------------------------------------------------------------  Eq-C
Eq_Gamma(C(F_1,...,F_k;z), C(G_1,...,G_k;z))

Le_Gamma(F_i,G_i) for every child i
----------------------------------------------------------------  Le-C
Le_Gamma(C(F_1,...,F_k;z), C(G_1,...,G_k;z)).
```

The original non-child operand tuple `z`, ordered source paths, provider
links, scopes and constructor tag must match. This includes conjunction,
whole-tuple union, Return/Request images, Bind, Call, rebind and consumers.
For Call, actual entry/receiver and designated consumer are in `z`. Bind's
continuation and current state are in `z`; no reordered sequence qualifies.
For a scoped binder, both sides retain that same binder in that same position;
the premises are checked under it. No projection of independent witnesses or
quantifier exchange is a congruence rule. A constructor that is not positive
in a child does not admit `Le-C` there; it can use an actual `Eq` proof only.
These restrictions are precisely what makes the source images monotone.

**Registered recursion.** A finite certificate pairs registered predicate
roots with their original source, interaction/guard and binder labels. For
every paired equation it provides a finite `Le` proof between the defining
operators, using only assumptions `X_r <= Y_pair(r)` at registered recursive
references. Every source-side alternative is covered. All recursive child
uses are positive. The corresponding `Eq` certificate supplies both
directions with complete alternative accounting. The checker verifies the
equation-pair table and local proofs once, without unfolding a cycle.

For the finitary source/abstraction grammars, soundness follows by induction
on finite derivation height. More generally the pointwise operator proof also
has a least-fixed-point argument: if `Y` is the right-hand least fixed point,
the operator comparison makes `Y` a pre-fixed point of the left operator, so
the left least fixed point is below `Y`. Least pre-fixed points exist for
monotone operators on the complete lattice of relations: the intersection of
all pre-fixed points is itself pre-fixed, and monotonicity shows its image is
again such a point and hence equal to it. No omega-continuity claim is needed
for that argument. In particular a universal logical binder over an infinite
domain does not by positivity alone justify finite-stage membership. Original
rigid binders in the source/abstraction derivation grammar stay external and
pointwise, as §3.7 specifies. The recursion rule is not an unchecked
coinductive assertion of arbitrary inclusion.

**Whole Function introduction.** Let `D_A,D_B` be the emitted admission roots
and `M_A,M_B` the complete membership roots **including ordinary descriptor
membership**, original residuals and all alternatives. The additional
ordinary resolution clause is

```text
same Function head, actual role/entry/consumer and non-coverage interface
Eq_Gamma(D_A,D_B)       Le_Gamma(M_A,M_B)
one original scope-preserving assignment/incidence map throughout
----------------------------------------------------------------  Function
Direct(A,B; the displayed finite proof DAG).
```

The ordinary descriptor terms at the submitted roots are part of the checked
input. The local active formation rules must expose their actual membership
and admission clauses; substituting a different hidden root is not permitted.
The rule does not accept bare assertions `D_A = D_B` or `M_A subset M_B`:
both must have the finite derivations just specified. Descriptor/role cases
outside these premises retain their existing ordinary resolution behavior.

For soundness, `Eq` gives the required complete-domain inclusion, and `Le`
gives complete-observation inclusion at each admitted challenge. Apply the
same final typed projection. This is the sufficient whole Function law of
typed core §9 with its premises proved syntactically, including every finite
future history. The fixed-domain rule of §8 is its paired-provider guarantee
leaf subcase. The parent query is introduced by the displayed `Function`
rule, not by composing successful child comparisons.

Accepting this calculus is an explicit **local resolution-conformance
hypothesis**. Source generation alone does not imply it. It is weaker than
global complete-query completeness: the only rule proving a parent query has
the displayed matched-interface, equal-domain and finite-clause premises.

### Theorem A-extension

Under §§2, 4–5's contracts, let `S_xi` be the complete original solution set
and `Q_xi(s,a)` retain all required local complete Function checks, legality,
scopes and dependencies. Then

```text
forall xi. forall s in S_xi. exists a. Q_xi(s,a),

projection_s { (s,a) | s in S_xi and Q_xi(s,a) } = S_xi.
```

**Proof.** Choose `a_s` from §5.2. Every original allowance implies its flat
union at the same fiber. Lemma 1 supplies each required local whole-provider
guarantee certificate. Lemma 2 removes every added common conjunct in the
admission and guarantee clauses without changing the old tuple. Thus the
complete constrained root retains all original challenges and observations;
arbitrary retained `Phi`, provider sharing and original witness scopes are
unchanged. Section 5.3 supplies the corresponding local query evidence.
All old solutions therefore extend. Projection in the other direction holds
because the original solution predicate is retained. QED.

This theorem proves representability **under the stated component and
incidence interpretation**, not from flat support syntax alone.

## 6. An independent conservative source-allocation abstraction

To state an all-view result without an execution-productivity assumption, use
the following proposed abstraction. It is a candidate under charter §9, not
a claim that current production already selects it.

### 6.1 Independent validity rules

A view is checked by a finite source derivation using ordinary value, role,
entry, provider, operation and continuation rules. The derivation retains the
whole non-coverage kernel and original binder tree. Its coverage obligations
are generated by these constructor clauses:

| Constructor | Coverage obligation inside its complete interface |
| --- | --- |
| Pure value construction | Evaluation remains pure; latent provider contracts remain separate. |
| Declared request/consumer | Its declaration-resolved contribution fits the allocated output. |
| Bind | The output covers both first-computation and suffix allowances, whether or not the suffix is reached. |
| Call | The output covers callee evaluation and the complete receiver output, including source-required argument/hygiene contributions. Actual entry still decides what executes. |
| Branch, if independently supplied | The output covers test and both branch allowances; the source kernel still chooses one branch. |
| Returned provider | Retain its original latent provider/typed paths; do not execute it at return. |
| Monomorphic recursive reference | Impose the same finite simultaneous obligations at the registered roots. |
| Public guarantee view | Retain the original source-node output `E_out`; a separate public allowance `W` must cover it at the same complete output view. This does not assign `E_out := W`. |

No local handler-image or opaque adaptation is included. Concrete subtraction
still requires its existing evidence; this abstraction does not invent it.
Annotation-free composition retains its hygiene-required contribution.

These clauses are a deliberately conservative interpretation of **allowances**,
not an assertion that all constituents execute. The source derivation is
checked before, and without reference to, the common scheme. It does not use
`Q`, an instance map, or `Direct(B_common,V)` as a validity premise.

For symbolic views, a finite local coverage proof may cite a retained symbolic
coverage obligation of the original scoped certificate. Checking/solving that
obligation remains an ordinary residual obligation; the theorem does not
claim a new solver for arbitrary `Phi` or operation predicates.

### 6.2 Soundness and the reachability distinction

Every request in a finite source derivation comes from an included primitive,
executed operand, branch, suffix or provider. Induction on that derivation
therefore proves that the allocated output covers it. Source bind preserves
the original request and resumed state; inclusion of an unexecuted suffix
adds permission but no execution. Recursive calls use the same simultaneous
obligations, and the proof still inducts on finite developments. No termination
or inhabited-intermediate-type premise is used.

This does not erase correlations: all coverage predicates are conjoined on
the original `nu,K,D` and provider/observation tuple. Operation compatibility,
authority and continuation obligations are the original source premises.

For example, when `g x` never returns in `f (g x)`, exact execution may never
expose `f`'s allowance. The conservative source rule nevertheless retains that
allowance obligation. An exact-execution-valid view omitting it can lie outside
this abstraction. This is an explicit precision boundary, not a source
counterexample or an implicit rejection policy.

### 6.3 The finite view class actually quantified over

Write `V_alloc(S)` for finite independently source-checked views such that:

1. they have a scoped derivation of §6.1 for the same source component;
2. their non-coverage kernel, value interfaces and typed paths match the
   original generated kernel after legal uniform grafts/renaming and retention
   of the original value/structural constraints. The primitive predicates and
   ordered constructor operands then have the identical leaves required by
   §5.3. No new adapter, value conversion or different entry is inferred;
3. their selected provider output bounds and root output bound are legal at
   the common scope and satisfy §5's incidence/variance conditions;
4. their additional predicates keep the same joint tuple and original scopes;
5. their local coverage certificate entails that every inventoried selected
   contributor `B_j` and the **original source-node outer endpoint** `E_out`
   are covered by the separate public allowance `W`.

Condition 5 follows by walking the finite constructor-allocation derivation
for the selected outward region. It is not inferred from observed support.
The inventory follows source composition edges, not every latent output in a
program indiscriminately. A latent stage outside that outward region needs its
own region and certificate.

The independent derivation supplies the old source constraint witnesses at
their original scopes: use its local endpoints for each generated source node,
its operation witnesses for the corresponding declaration occurrence and its
same provider for each resolved name. Induction on the constructor inventory
verifies the original constraints. This is ordinary source-generation
completeness for this supplied derivation, not a requirement that `V` first be
an instance of the common scheme.

In detail the certificate associates a local endpoint with **each original
source occurrence**, independently of the public-root annotation. Literal,
declaration, import and explicit annotation nodes retain their required
endpoint equations; source edges refer to those same local endpoints.
Fresh unconstrained allocation nodes may be chosen by the independent
derivation. The public-view rule adds a separate `W` and its coverage clause;
it never replaces the original output node. Thus `E_out = Read` and
`W = Read,Write` are compatible when the source coverage certificate proves
that widening. This is the endpoint map used to reconstruct `C_G`, including
fixed constraints.

Arbitrary semantically sound Function contracts are not asserted to have such
a finite derivation or kernel alignment. Value principality beyond the
supplied original value/structural obligations is also not proved here.

## 7. Theorem A-allocation: the actual common export

Assume §§2–6's contracts. For every independently valid finite
`V in V_alloc(S)`, there is an ordinary finite whole-copy/graft/direct-query
use `m_V` through the **designated common root**, preserving all public
solutions at their original binder scopes.

Let `C_V(v)` be the public solution predicate with its original scope tree.
The exact projected extension statement is

```text
forall v satisfying C_V.
  exists original-scope s,a,evidence.
    C_G(s) and Link(s,v) and Q(s,a)
    and Direct(B_common(s,a), R_V(v)).
```

All existential notation here respects that tree. It must not be moved
outside a rigid binder on which its witness depends. The one finite `m_V`
contains the copied graph and retained constraints; it does not choose a fresh
source solution for each runtime challenge.

**Construction and proof.** Use §6.3's independent derivation to fill the old
source endpoints and joint residual; write its selected bounds as `B_j` and
its outer bound as `W`. Keep each old `B_j` exactly as supplied, including fixed
declaration/annotation constraints. Set only the fresh common coordinate
`a := W`. Its scope legality is a view-formation premise.

The source allocation derivation gives every `B_j` and the original `E_out`
covered by `W`. Consequently, at every public solution,

```text
Allow(flat{E_out,B_1,...,B_n}) implies Allow(W),
flat{W,E_out,B_1,...,B_n} = W.
```

This is same-fiber absorption, with all old constraints retained. It is not an
equation `B_j = W` or `E_out = W` and requires neither a complement term nor
subtraction. As §5.2 specifies, the totality witness is not an equation imposed
on every presentation solution, so choosing `a := W` is permitted even when
the old canonical union is strictly smaller.
Lemma 1 gives the local `Q` certificates. In parent admission, the original
predicate `Bound_j(B_j,u_j)` remains incident to the common view of that same
provider. Lemma 2 therefore shows that the common conjunct neither excludes
an admitted view challenge nor admits a new one for this old witness.

In the complete output clause, the same joint source kernel and original
bound constraints remain; the fresh common outer allowance is `W`. The
finite proof DAG for the submitted query is now explicit:

1. Use the referenced allocation clauses to derive `Cov(B_j,W)` and
   `Cov(E_out,W)` at their original scopes.
2. Apply `Absorb` to each old/common provider conjunct in `D_common`.
   Apply `Eq-C` through the unchanged source/admission clauses. The finite
   recursive equation-pair table, where present, is the copied source table.
   This gives `Eq(D_common,D_V)`.
3. In the membership roots, use the same absorption at retained incidences,
   identity only for unchanged non-coverage/descriptor predicates, and
   `Guarantee(E_out,W)` at a public guarantee that is wider than the original
   source-node bound. Changed selected descriptor operands use §5.1's actual
   `Bound`-leaf exposure and the appropriate `Guarantee`/`Absorb` proof; they
   do not use an identity leaf. Lift these leaves by `Le-C`, with the same scoped
   recursive pairing. This gives `Le(M_common,M_V)`; the view's source
   certificate is exactly the matching finite constructor inventory of §6.3.
4. Apply `Function` once, to the actual input roots

```text
Direct(B_common(s,W), R_V(v)).
```

All alternatives, future providers and continuations are those of the complete
paired kernel. This constructs evidence for this one query; it does not infer
it by composing `R_G <: B_common` and `R_G <: V`. No original fixed bound is
overwritten to obtain the proof.

Whole freshening/grafting copies the original scope tree and every incidence.
The copied independent derivation supplies witnesses for each public solution
at those same binders. Thus the displayed extension holds. Conversely the use
retains `C_V`, so its projection adds no public solutions. This is the ordinary
finite use of the certified-use theorem, now with evidence at the actual
common export. QED.

### What is and is not proved by this theorem

The theorem allows the complete original residual required by the acceptance
criteria. The common root is an actual resolver operand, not a display of a
hidden old root. Its common ports coexist with semantically active old
contracts; an implementation that erases the latter does not satisfy §5.

The theorem does not prove a stronger presentation with all those old
contracts erased, a fixed old solution enlarged to all common inputs, or
factorization of views outside `V_alloc(S)`. Nor does it establish that every
accepted source value/interface derivation is in that class. Its quantifier is
exactly `forall V in V_alloc(S). exists m_V`.

### Corollary A-allocation-abstraction

For production Option 2, define `V_alloc,H(S)` independently by §6's source
allocation rules together with its declared §3.7 abstraction grammar, the
paired `W,Z` contracts/invariant parameters and the unchanged-admission
certificate. The source and guard clauses must have the finite alignment and
coverage proofs just used in §7; no final common-query success is a premise.
Views with a different, unmatched abstractor are outside this subcase.

For every such finite view, the same construction `a := W_public` retains all
old source endpoints. Here `W_public` is the allowance of §7 and is distinct
from the abstraction relation named `W` in §3.7. The base and hard-envelope
`Eq`/`Le` proofs lift through `H` by its two-parameter monotonicity; the finite
certificate uses the displayed positive operators and registered equation
pairing. The single `Function` rule then accepts the **actual abstracted
common root** against the actual abstracted view root. Hence

```text
forall V in V_alloc,H(S). exists original-scope finite m_V.
```

At an arbitrary old solution already interpreted by that declared production
grammar, A-extension's identical old/common base and hard-envelope clauses
likewise remain identical under `H`. Thus its exact forgetful projection is
preserved. Activating an unrelated extra rule that violates an old guarantee
would not satisfy the hard-envelope or paired-grammar hypotheses.

This corollary includes unanchored conservative root extras. It neither
requires production to equal `P_ref` nor proves that all independently valid
production views share the required grammar/parameter certificate.

## 8. Named source forms and applicability

| Form | Selected common guarantees | Preserved information / premise |
| --- | --- | --- |
| `call f x` | Provider output and outer call output. | Original argument/provider, entry and value checks. |
| `twice f x` | Repeated provider output and outer bind output. | Both call occurrences, current state and ordered suffix; no multiplicity in flat support. |
| `choose cond f g x` | Both provider guarantees and the branch output. | Independent branch rule, branch dependency and original value checks. |
| `higher f g x` | First-stage output, returned-provider output and final outward region. | Function-valued first argument and second argument remain distinct; same returned provider; future arguments fixed. |
| `compose f g x` | Relevant outward `c` guarantees. | Intermediate/input `b` is retained unchanged; source Force/rebind and hygiene correspondence is a separate supplied source premise. |

These identify the effect portions to which the theorem applies. They do not
certify the entire seven accepted schemes or every possible instance of their
value/capture interfaces. In particular this proof never applies scalar
guarantee monotonicity to `compose`'s input `b`.

No productivity assumption excludes `never`, divergence or an unreachable
branch from the allocation abstraction. Scope closure, non-coverage alignment
and the actual source constructor contracts remain material restrictions.
Current HIR supports only the much smaller application-free fragment; the
source application/branch constructors here are mathematical derivations,
not newly implemented HIR forms.

## 9. Why source hypotheses alone are insufficient

There are two distinct independence issues.

**Unspecified extras.** Two endpoint interpretations may retain identical
source labels and four Function children but admit different extra behaviors.
An emitter's source-incidence checks alone do not compare those alternatives.
Approved Option 2 permits extras; §3.7 supplies a conditional exhaustive
source-plus-abstraction grammar and a local proof that paired alternatives
preserve the needed containment. It does not exclude extras by definition.

**Incomplete direct resolution.** In a no-capture, fixed-domain fragment,
consider genuine provider guarantee bounds `Read` and `Read,Write` with the
same non-coverage envelope. Lemma 1 gives containment. A sound resolver that
accepts only equal guarantee bounds in that otherwise unspecified fragment
may reject the widening. Source emission does not create its missing evidence
alternative. This is a countermodel to source-conformance-implies-resolver-
completeness, not a Yulang source counterexample and not a change to a
mandated existing comparison case. Section 5.3 names the additional local
resolution clauses required by the conditional theorem.

Neither independence issue proves that a richer carrier is necessary. Both
can be addressed with formation and proof rules over the existing complete
presentation. Adopting those rules remains a concrete semantic decision;
implementing them remains separately unauthorized.

## 10. Work remaining after these conditional results

| Obligation | Status in this note |
| --- | --- |
| Pure structural FMP / regular completion | Already A in the [fence-completion theorem](2026-10-04-structural-fmp-fence-completion.md); no extra source restriction needed. |
| Finite local source-to-constrained-root decoding | C-realization proves the source base. C-abstraction extends it to declared positive conservative root grammars under paired envelope/admission/transport certificates. |
| Common descriptor and every-old-solution extension | A-extension proved for scoped guarantee-only active views. |
| Every finite independently valid allocation view | A-allocation proved with explicit non-coverage/value and scope premises; A-allocation-abstraction covers paired Option 2 grammars in `V_alloc,H(S)`. |
| Current production satisfies active root membership/admission and whole transport | Not established; current retained-artifact tests do not assert this. |
| Production may admit non-source-witnessed root extras | Selected by approved Option 2 at `74eab866`; a concrete exhaustive grammar is still unselected. |
| The allocation abstraction / local complete-query rules are selected | Not selected by this research note. |
| Every accepted source/value/capture interface belongs to the theorem envelope | Not established. No rejection rule is inferred. |
| Arbitrary complete adapters, local handler images, mutable state | Outside this theorem. |
| Effective solving of every retained symbolic residual and all lifecycle gates | Not supplied by these finite conformance/projection proofs. |
| Production implementation | Unauthorized. |

The useful next implementation-facing object is the finite emission and
comparison contract, not a global assumption of adequacy or principality.
The remaining adoption and source-coverage obligations are visible rather
than hidden in `forall s exists a` or `forall V exists m_V`.

## 11. Verification and review

The [finite checker](../../tools/research_source_allowance_contract.py) passes
648 complete joint absorption cases and 648 allocation-view cases over 3,200
typed provider pairs. It includes conservative may-bounds, dependent request
arguments, correlated providers, nonreturning prefixes and fixed original
output bounds. Explicit negative cases distinguish the forbidden shortcuts.
These are finite characterizations, not proof of unbounded histories or
actual source-generation/scope conformance.

Independent M3 compiler-referee and specification-auditor review was followed
by a fresh compiler-referee repair review. The two accepted major findings
were the missing explicit parent certificate rules and accidental identification
of old `E_out` with public `W`. Both were repaired and closed. The delta review
found no remaining blocking/major issue in its scope and one minor request to
make changed ordinary descriptor-leaf exposure explicit. That clarification
is now in §§5.1 and 7, checked by primary diff inspection. The specification
audit found no conformance issue in the conditional claims and did not approve
their adoption. Exact review scope, finite evidence and remaining gates are in
the [proof record](../progress/2026-10-05-source-contract-conditional-proof.md).

After approved Option 2 arrived, a separate independent compiler-referee and
focused specification review checked §3.7, the abstraction corollary and their
dependencies. Both reported no blocking, major or minor finding. The extended
finite model passes 110,592 guarded closure cases and 884,736 two-parameter
comparisons, including a constant extra with no source anchor. Those reviews
do not select the concrete abstraction primitives or prove production/source
coverage beyond the explicitly stated conditional envelope.
