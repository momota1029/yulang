# Coupled effect-interface core (draft)

- Date: 2026-10-01
- Status: Draft; non-authoritative; not implementation-ready
- Scope: one mathematical carrier for ordinary effects, shallow handlers,
  typed-family constraints, and SCC lifecycle transport
- Implementation authority: none
- Inputs: user direction to prefer a small unified theory; the reviewed
  intrusion redesign charter; current effect and handler proof records

## Purpose

This note consolidates the preferred *shape* of the successor theory. It is
not a selected effect calculus and does not supply missing source semantics.
Its organizing idea is that source constructs relate complete typed
computation interfaces. Row operations, handler residuals, callback effects,
and SCC lifecycle steps are derived views or relational compositions, rather
than separate source-site constraint systems.

The design target remains soundness and principality relative to the selected
expressible abstraction. Exact execution traces are the soundness reference;
the inferred interface may conservatively over-approximate them. No
continuation-use or linearity discipline is required without independent
language-design authority.

## One semantic carrier

Fix imported identities `ρ`. Let `β` be the identities owned by one component
and `ν` an admissible assignment to them. For each complete component root,
an interface records its value type and every immediate or latent computation
view observable by clients. A computation view contains a may-bound on typed
requests, symbolic request arguments and operation payload/result
constraints, and the sharing among arguments induced by source binders. It
also retains the dynamic handler context needed to determine which requests
can be handled. These are semantic distinctions: changing them can change an
admissible type assignment, client observation, or handler transition.

Allocation-site labels, request occurrence IDs, owner paths, and route
certificates are not themselves observable interface coordinates. A finite
presentation may use them as indices and proof witnesses. It must preserve
the source-derived sharing equivalence and dynamic boundary behavior, modulo
capture-avoiding renaming, but it need not preserve arbitrary label identity.
In particular, an `owner ID` is bookkeeping for a source binder; the
mathematical relation depends on which occurrences share that binder, not on
the numeric or syntactic spelling of its ID. Likewise, a route record may
witness visibility but does not define visibility independently of the source
handler transition.

The component meaning is one extensional relation over assignments and
source-observable root interfaces, modulo renaming of bound identities:

```text
Rel_C(ρ) ⊆ { (ν, O) | ν assigns β and O is a complete observable root interface }
```

The relation couples roots, request behavior, typed-family denotations,
source-owned sharing, and handler visibility. A row or constraint formula is
a finite presentation or projection of this relation. Neither an obligation
ledger nor a dependency edge is an additional semantic coordinate. In
particular, a typed-family invariant restricts which `(ν,O)` pairs belong to
`Rel_C`; solving may reindex that predicate or discharge it with proof, but
materialized row comparison cannot recreate it after it has been dropped.

For transport statements, write a finite presentation as
`p = (V, M, Q, K, D)`: value views `V`, may-support coordinates `M`, typed
request facts `Q`, symbolic formulas `K`, and incidence `D` connecting each
formula to the views that depend on it. Its denotation `⟦p⟧_ρ` is a set of
`(ν,O)` pairs; `K` contributes by formula satisfaction, while occurrence and
owner labels in `Q,D` present the source-derived sharing relation. `D` also
records how the implementation preserves formula-to-view dependencies. Thus
`K` and the induced sharing predicate present semantic restrictions, while
numeric labels and `D` are transport bookkeeping, not extra coordinates in
the mathematical carrier. A post-solve or
post-handler presentation must denote the required transformed relation. If
a formula is discharged, the proof must establish equivalence for the
affected views; equality of materialized rows is not such a proof.

The meaning of typed request inclusion and the source rule that creates a
shared invariant argument group still need definition. The core does not
assume that support inclusion, common-witness compatibility, and handler
eligibility are the same predicate. They are observations of different
coordinates in the same coupled relation: request denotation, symbolic type
admissibility, and dynamic boundary visibility respectively.

#### Source ownership and visibility are judgments, not extra mechanisms

The economical candidate is one source typing/evaluation judgment indexed by
the ordinary type-variable environment and the current machine configuration.
An operation request carries the instantiation of its declaration binders
that the typing derivation assigned to that occurrence. Two occurrences share
an invariant argument exactly when the derivation refers to the same owned
binder identity; equal operation heads, equal concrete types, or membership in
one inferred row do not create sharing. The common assignment to that binder
then constrains every incident root, request, and latent interface in `Rel_C`.
`g(o)`, occurrence incidence, and `GroupEq` are notation or finite witnesses
for this single binder environment, not a semantic grouping operation. The
source rule that chooses which declaration binders remain shared across
applications, callbacks, and recursive roots is still open; until derived,
this candidate cannot decide those cases.

Likewise, handler visibility is decided by the ordinary ordered machine
search over its complete configuration and source typing relation. There is
no second `Capture` store or family-level grant bit: `Visible(q,h,κ)` is
relative to one candidate handler activation `h` and states that the source
derivation and complete active configuration permit this request occurrence
to reach that activation. Request origin, binder assignment, frame
entry/unwind, and saved-continuation re-entry are coordinates of the common
relation when observable. A route record or capture-incidence map may witness
the derivation, but cannot independently grant visibility.
The callback annotation, helper, escape, and force rules that derive this
judgment remain an explicit source-semantics obligation. This formulation
keeps two genuinely different observations—type sharing and dynamic reachability—
inside one relation without identifying them or making either a new solver
mechanism.

#### Candidate-formulation comparison

The current preference is the extensional `Rel_C` over assignments and
complete observable interfaces, with source constructs interpreted as
relations and compiler phases represented by relational restriction,
composition, and capture-avoiding transport. This is the smallest candidate
that currently preserves both symbolic typed-family invariance and the
distinction between static type sharing and dynamic handler reachability.

| Candidate | Economy | Compositionality and principality | Current disposition |
|---|---|---|---|
| Independent `Sel_s`, `Demand`, typed-family obligation, and route rules | Low: each site adds a selector or obligation kind | Duplicates semantics across solving, residualization, and lifecycle phases; principality must be re-established per kind | Treat as implementation projections or proof witnesses unless source semantics proves a fundamental distinction |
| Ground rows as the sole interface | Superficially small | Cannot preserve invariant family arguments symbolically or their correlation with shared requests; post-materialization reconstruction is invalid | Reject for the required symbolic invariance |
| One complete relational interface with source-judgment composition | One semantic carrier plus ordinary source judgments | Composition can derive splitting, filtering, subtraction, callback behavior, and lifecycle transport; principality is stated relative to the chosen expressible abstraction | Preferred candidate; soundness, finite presentation, and principality remain proof obligations |
| Exact continuation-sensitive trace sets | Semantically precise | May demand usage or linearity structure absent from the language and a richer inference domain | Use as a soundness reference; do not require exact inference absent independent language justification |

This preference does not assert that all operations collapse to one
mathematical function. Distinct source constructs can induce distinct
relations. The economy claim is that they act on the same interface carrier
and obey common relational composition and transport laws. Source-specific
selectors, route classes, or obligation variants need separate semantic
justification. Row splitting, filtering, and handler subtraction should be
derived as projections or residuals of the source relation; generalization,
instantiation, and intrusion should preserve its denotation through binder
renaming and assignment transport. A solver may keep specialized data
structures as bookkeeping, provided they neither add semantic choices nor
discard symbolic predicates.

#### Existing names projected from the common relation

The vocabulary used in earlier proof records should not be mistaken for
independent semantic mechanisms. The intended factorization is:

| Existing name | Meaning in the common theory | Retain as |
|---|---|---|
| `Sel_s` | A witness that one typed request in a support projection is covered by a request in another projection | A finite inclusion witness or proof term; its alternatives are not semantic choices |
| `Demand` | The source evaluation context composes a suspended computation when it needs the resulting value | A derived property of the ordinary value/computation judgment, not a site selector |
| Typed-family obligation / `FamAgree_A` | The shared owned assignment must satisfy every incident invariant argument predicate | A symbolic predicate in `Rel_C`, transported with its owner and incidence |
| Route evidence | One source handler-search transition makes a request visible, selected, or forwarded in a specific activation | A derivation witness for dynamic visibility, not an independent grant or row constraint |
| `P`, `Theta`, `K`, `D`, parent and occurrence maps | Reindexing or presenting one relation while preserving its identity and dependency structure | Transport witnesses and finite-presentation metadata; the denotation changes only by the stated relation image/reindexing |

Only three distinctions presently have independent semantic force: source
value versus computation behavior; a common source-owned identity versus
independent identities; and a request's dynamic visibility in the active
handler configuration. Even these are not separate solver constructs: they
are coordinates or predicates of the same source-indexed relation. The
particular names above do not justify adding a grammar form, a new kind of
typing judgment, or an obligation algebra. If later source semantics proves
another distinction fundamental, add it to the relation with an explicit
observation and preservation theorem before introducing representation
machinery for it.

This sets a proof economy test for every proposed rule: identify the ordinary
source transition or relation operation it presents; show how its denotation
follows by projection, restriction, composition, image, or capture-avoiding
reindexing; and state which common transport laws apply. A rule that cannot be
derived this way is a candidate for an actual source-level distinction and
must be justified there, rather than copied from an Oracle stage boundary.

#### One denotational row relation (candidate)

For a fixed complete assignment `ν`, interpret a typed row jointly with its
source-owned family-instantiation identities. Let `g(o)` identify the owned
type identity or tuple whose assigned value supplies the invariant argument
of occurrence `o`; it is not a fresh value chosen independently during row
comparison. Occurrences with no shared binder receive distinct local
identities. This ownership comes from the source typing relation and is
transported with the complete relation, not selected at a row-comparison call
site. If `ArgDen_A(o,ν)` interprets the allowed complete argument tuple of
occurrence `o`, define:

```text
J_R(ν) = { Q |
  ν(g) ∈ ⋂_{o:g(o)=g} ArgDen_A(o,ν) for every binder g,
  Q = { (head(o), ν(g(o))) | o ∈ occurrences(R,ν) }
}
TypedRow(R,ν) = ⋃ J_R(ν)
RowSub(R,S,ν) iff J_R(ν) ≠ ∅ ∧ J_S(ν) ≠ ∅
                   ∧ TypedRow(R,ν) ⊆ TypedRow(S,ν)
```

Open tails are evaluated in the same assignment before taking this relation;
they are not replaced by a second source-site rule. `RowSub` is the candidate
meaning behind row splitting, filtering, and row comparison. Its supports are
compared at the same complete type assignment; binder values are not
existentially projected across assignments first. At fixed `ν`, `J_R` is
empty or contains the one request set selected by the owned binder values. A
solver may expand subset into finite witness formulas, but a `Sel_s`/`Demand`
pair list then records a derivation of membership, not an additional semantic
choice. The nonempty-`J` premise prevents an inconsistent shared binder from
making inclusion vacuously true by projecting to an empty row.

The common-witness condition is represented by the owned assignment
`ν(g) ∈ ⋂ ArgDen_A` for each shared binder. Existentially projecting away `g`
would retain only the yes/no fact that an intersection is nonempty and lose
which value remains coupled to roots and requests. Typed-family invariance is
therefore a predicate in the same solution relation, not a second obligation
kind and not a post-materialization reconstruction. If the source does not
establish shared ownership, there is no shared identity and no intersection
constraint is imposed. Handler eligibility remains a property of the source
handler transition on typed requests and active boundaries, not a variant of
`RowSub`.

Under this candidate, splitting is a projection of the joint relation while
preserving its binder environment; union combines the occurrence views and
their binder constraints. Filtering is restriction of the joint request
relation, and handler subtraction is the residual support projection of the
relational handler image. Any coverage witnesses or route records used by a
solver are proof evidence for those operations. This equation is conceptually
compact, but still conditional on the source meaning of duplicate family
occurrences, the concrete argument denotation, and the actual source rule that
creates a shared-instantiation batch. Until those are established, it is a
common candidate relation, not the selected successor semantics.

Splitting does not in general justify discarding the shared binder context.
For occurrence-disjoint rows `R` and `S`, if no binder is shared across the
split, their joint assignment factors and their support projections union.
If the split separates occurrences that share a binder, the assignment
condition for that binder must be intersected before projection. For example,
with argument domains `{int,bool}` and `{bool,str}`, only the shared value
`ν(g)=bool` satisfies both pieces; independently solving fresh group values
admits `int` and `str` as well. The relational split therefore carries the
original binder and its full incidence; a solver may factor it only after
proving the factorization condition. This is a direct criterion for when row
splitting is a harmless view and when it would lose a typed-family constraint.

#### Algebraic consequences at one fixed assignment

For a fixed `ν`, write `supp(J_R(ν)) = TypedRow(R,ν)`. The row view has a
small algebra that follows directly from the joint relation. When the source
row constructors are interpreted by occurrence union and restriction, and
their shared-binder constraints are evaluated in the same assignment, support
union holds when both input fibers are nonempty:

```text
supp(J^K_{R ∪ S}(ν)) = supp(J^K_R(ν)) ∪ supp(J^K_S(ν))
supp(Filter_φ(J^K_R(ν))) = { q ∈ supp(J^K_R(ν)) | φ(q) }
Filter_ψ(Filter_φ(J^K_R(ν))) = Filter_{φ ∧ ψ}(J^K_R(ν))
```

Here `K` is the source-derived symbolic predicate of the complete interface,
including shared-binder intersections established before any request is
filtered, and
`J^K_R(ν) = { Q | K(ν) ∧ Q = { (head(o),ν(g(o))) | o∈R } }`.
The notation keeps that persistent predicate explicit in the filter laws.

More generally, for a semantic interface relation
`Rel ⊆ { (ν,O) }`, write `Q(O)` for its typed-request support coordinate and
`O[Q←Q']` for replacing only that coordinate. Filtering is the image of a
semantic coordinate map:

```text
Filter_φ(Rel) =
  { (ν,O[Q←Q(O) ∩ φ]) | (ν,O) ∈ Rel }
dom_ν(Filter_φ(Rel)) = dom_ν(Rel)
```

The domain equation follows because this map changes only `Q`; every
satisfying valuation remains represented, including fibers whose filtered
support becomes empty. At the presentation level, a filter implementation
must produce `p'` with denotation `Filter_φ(⟦p⟧)` while retaining `K` and its
incidence `D`; they may be projected away only after their dependencies have
no retained observation or a proof discharges them. Thus filtering preserves
the satisfying fiber rather than asking the surviving row to recreate it.
Projection to roots after filtering preserves the original root solutions;
projection that also observes the effect row returns the intentionally
filtered rows together with their original symbolic correlations.

Filtering also commutes with an injective capture-avoiding reindexing. Let
`T_θ(ν,O) = (θ*ν,T_θ(O))` be the induced map on assignments and complete
observations, and transport the predicate with it so that
`q ∈ φ` iff `T_θ(q) ∈ φ_θ`. Then elementwise:

```text
T_θ(Filter_φ(Rel)) = Filter_{φ_θ}(T_θ(Rel))
```

Both sides contain exactly the images of `(ν,O)` in `Rel` with request support
`T_θ(Q(O) ∩ φ) = T_θ(Q(O)) ∩ φ_θ`; all other observable coordinates are
mapped by the same `T_θ`. At presentation level, this law requires applying
`θ` to `K` and its occurrence/view map to `D` together. It therefore supplies
one reusable commutation lemma for row filtering through use-site freshening
and injective intrusion, conditional on filter-predicate naturality. It does
not cover a non-injective parent quotient.

Solving may use a non-injective type substitution `σ`. If its induced map
`T_σ` substitutes all type endpoints and typed-request arguments, while
leaving request occurrences, family-ownership groups, and handler identities
distinct, and if the filter is substitution-natural
(`q ∈ φ` iff `T_σ(q) ∈ φ_σ`), then the same set-image proof gives:

```text
T_σ(Filter_φ(Rel)) = Filter_{φ_σ}(T_σ(Rel))
```

Injectivity on type variables is unnecessary because both sides are images of
the same request-wise restriction; several typed arguments may map to one
argument while their source occurrences stay distinct. The presentation must
substitute `K` uniformly and preserve its occurrence incidence. This is only
formula-transport naturality: it does not prove that the solver substitution
preserves the full solution fiber, nor does it authorize a non-injective
parent map that merges ownership, request, or boundary identities.

The same row restriction commutes with generalization when it acts only on
the interface coordinates that generalization retains. Write a fixed-outer
relation as `Rel ⊆ { (ρ,β,O) }`, where `β` are locally owned identities and
`O` is the complete exported interface. Define
`Gen_β(Rel) = { (ρ,O) | ∃β. (ρ,β,O) ∈ Rel }`. For a restriction map
`F_φ(ρ,β,O) = (ρ,β,F_φ(O))` that leaves `ρ` and `β` fixed, then:

```text
Gen_β(F_φ(Rel)) = F_φ(Gen_β(Rel))
```

Proof: either side contains exactly `(ρ,F_φ(O))` for which there exists a
local assignment `β` with `(ρ,β,O) ∈ Rel`. The existential witness is
unchanged because `F_φ` does not inspect or alter hidden `β`. If a filter
depends on local information absent from the exported interface, this equation
does not apply: that dependency must remain symbolically represented in the
generalized relation rather than being recreated from a materialized row.
This is a relational commutation law, not a claim that the current scheme
presentation can express every such existential projection.

The first equality concerns support only. It does not say that the joint
assignment relation factors across a split: when a binder occurs on both
sides, the shared assignment and its incidence remain in force. The second
and third equalities define `Filter_φ` as restriction of the existing request
coordinate, not reconstruction of a new `J_{filter φ(R)}` from the surviving
occurrences. The full interface predicate and ownership incidence stay in
place even when filtering removes every request that originally witnessed
them. A predicate that inspects route or activation history is outside this
row algebra and belongs to handler applicability.

This distinction is required by the symbolic lifecycle invariant. The
occurrence-derived intersection in `J_R` is a convenient row view, but by
itself it is not a durable representation for residualization: recomputing
that intersection from a filtered row can forget a constraint whose request
was removed. The filtered interface must retain the original fiber predicate
`K` (or an equivalent proof-carrying restriction of the complete relation).
The `Filter_φ` equations are valid on that retained relation; an equation
between freshly reconstructed row-only `J` values is not claimed.

Handler subtraction does not follow from set difference alone. It is the
residual support projection of the handler's relational image on
continuation-bearing computations. For a handler proven total on the relevant
concretization, the residual request support is a consequence of that image;
an incomplete handler or unknown route cannot be erased by applying the
filter equations above. This distinction keeps row restriction general while
deriving removal only from the declarative transition relation.


The frozen typed-family use probe is a useful consistency check on binder
ownership. Its generalized `generic` has result type `α` and effect request
`ask<α>`; the same owned `α` must feed both views. The two external uses map
that identity independently, then the enclosing handlers constrain one copy
to `int` and the other to `bool`. In the candidate relation, the request's
`g(o)` is that already shared scheme binder, so its request projection remains
coupled to the result type; it is not a new row-only binder. This matches the
observed independent-use behavior, but the frozen probe is only characterization
evidence and does not prove the Oracle's internal symbolic transport. The
fixture and its artifact limitation are recorded in
`notes/progress/2026-10-01-intrusion-typed-family-independent-instantiation-probe.md`.

#### Closed point-row expansion

The joint relation has an exact finite formula on closed rows when every
occurrence denotes one point argument tuple. Write `args(o) ≈ args(p)` for
componentwise equality in the chosen type interpretation, and define
`GroupEq(R,ν)` to require the assigned binder value `ν(g)` to equal each
occurrence argument tuple in its group. Then:

```text
RowSub(R,S,ν) iff
  GroupEq(R,ν) ∧ GroupEq(S,ν) ∧
  ⋀_{o∈occurrences(R)} ⋁_{p∈occurrences(S), head(p)=head(o)}
      args(o) ≈ args(p)
```

An empty disjunction is false. `GroupEq` is exactly the nonempty-`J` condition
for point-valued arguments at this fixed assignment; after it holds,
`TypedRow` is the finite set of typed requests carried by the occurrences.
The final conjunction is then
ordinary set inclusion, whose witness for each left request is one matching
right occurrence. This derives the familiar finite pair alternatives from
one denotation, while retaining the shared-binder equality formulas in the
same symbolic relation. It also shows why matching pair data cannot replace
`GroupEq`: the left and right rows can each be internally well-formed yet
have no common typed request at a required family head.

This lemma is exact for the stated point interpretation and source-owned
groups. It does not decide how source syntax creates those groups, extend to
interval/compound arguments, or prove that the compiler's current
`InvArgs` generation is equivalent to `GroupEq`.

#### Why the support projection cannot replace the joint relation

Even an exact `TypedRow` support view is not a complete function/effect
interface. Consider the finite joint relation

```text
J = { (a, result=a, request=F<a>) | a ∈ {int,bool} }
```

Its result marginal is `{int,bool}` and its request-support marginal is
`{F<int>,F<bool>}`. Their Cartesian product additionally contains
`(int,F<bool>)` and `(bool,F<int>)`, neither of which belongs to `J`. Thus a
row may be the exact support projection and still lose which result and
request argument came from the same owned binder. Generalization, callback
composition, handler matching, and fresh instantiation must carry `J` or an
equivalent symbolic constraint relation; rebuilding it from the two
materialized marginals is unsoundly permissive. This is why `TypedRow` is a
view used for support inclusion, not the authority for the complete scheme.

#### Why row inclusion must retain complete assignments

At one fixed complete assignment, inclusion has the finite expansion

```text
RowSub(R,S,ν) iff J_R(ν) ≠ ∅ ∧ J_S(ν) ≠ ∅ ∧
  ⋀_{q∈TypedRow(R,ν)} ⋁_{p∈TypedRow(S,ν)} q = p
```

This is an equality of the complete assigned request sets. Do not union the
`TypedRow` projections across assignments before comparing. For a concrete
counterexample, let `R` contain two independently owned `F` occurrences with
arguments `a,b ∈ {int,bool}`; at assignment `a=int,b=bool`, its complete
request set is `{F<int>,F<bool>}`. Let `S` contain two `F` occurrences sharing
one binder `c ∈ {int,bool}`; every complete assignment to `S` yields only
`{F<c>}` because the duplicate requests have one shared argument. At that
same complete assignment, no `S` row covers `R`. Yet after independently
unioning supports over all assignments, both sides project to
`{F<int>,F<bool>}`, and inclusion falsely appears to hold. The full joint
relation rejects the case without inventing a source-site selector.

For interval-valued arguments, `ν(g) ∈ ⋂ ArgDen_A` is part of the same
assignment predicate. Any finite formula or solver normalization must retain
that selected value and all root/request correlations while expanding the
pointwise support inclusion. The support marginal alone cannot certify
coverage or principality.

## Source constructs as relational composition

Each source construct denotes a relation from its input interfaces and
constraints to its output interface. Sequential evaluation composes those
relations; may-effect join is the support projection of that composition.
The following familiar operations then have one derivation pattern:

- **Row inclusion and filters:** constrain the request-support projection of
  two interfaces. Filtering is the corresponding restricted interface
  relation, retaining all symbolic endpoint and owner constraints that its
  result depends on.
- **Splitting and union:** project or combine request-support coordinates.
  This alone says nothing about whether a handler transformer distributes
  over a split; that equation requires a theorem for the transformer.
- **Callbacks and latent effects:** compose invocation of one interface with
  the callback interface supplied to it. The callback's possible requests
  become part of the caller's computation according to the source evaluation
  relation. They are not inferred from Oracle weight movement.
- **Shallow handlers:** relationally map the full continuation-bearing
  computation interface through the source handler semantics. The residual is
  the output support projection. A request can be removed only when the
  semantics proves that every request represented by that portion is covered
  and eligible at the relevant activation. Activation-specific visibility is
  part of the semantic relation; a route certificate is only derivation
  evidence that the handler transition respected that visibility, not a
  separate semantic coordinate or row selector.

These descriptions are a common denotational interface, not a claim that each
operation is a homomorphism. In particular, a handler may fail to preserve
union exactly because a may-row forgets correlations between requests and
continuations. Soundness requires an over-approximation of the relational
image; principality asks for the most-general representable result in the
chosen interface language.

#### Composition over a shared assignment

The static interface composition used below is ordinary relational join with
one fixed outer assignment and one identity environment. For predicates
`R(ρ,ω_R,X,Y)` and `S(ρ,ω_S,Y,Z)`, first reindex locally owned identities so
that distinct owners are disjoint and source-shared owners remain identical.
Then let `ω` assign their union, with restrictions agreeing on any
source-shared identity; its type-variable component is `ν`. Define:

```text
Comp(R,S)(ρ,ω,X,Z) iff
  ∃Y. R(ρ,ω|Ω_R,X,Y) ∧ S(ρ,ω|Ω_S,Y,Z)
```

The existential is only over the intermediate interface `Y`. It does not
choose separate type assignments for the two premises: both predicates see
the same `ρ`, and every shared owned identity has one value in the joined
assignment. Their symbolic formulas therefore compose by conjunction before
any local identity is projected away. For example, if `R` requires
`FamAgree_A(B₁,g,ν)` and `S` observes the same source-owned `g` in a result or
request, the composite retains both facts under that one `ν(g)`; it cannot
solve each side with independently chosen family arguments and then join only
their row projections. Conversely, independent source-owned binders are
alpha-renamed apart before composition and can be related only by an explicit
source constraint in `R` or `S`.

This is the static counterpart of state-threading execution bind: both join
relations at their shared interface and preserve the identity environment.
The execution relation additionally carries resumable continuations and
dynamic machine state; those are its intermediate coordinates, not extra
static row rules. Support union, callback invocation, filtering, and handler
image can thus be derived as projections or transformations of a relation
composed under one valuation. The algebraic definition is straightforward;
the open adequacy obligation is to prove that source typing creates exactly
these shared identities and intermediate interfaces.

**Associativity at one identity environment.** Let `R,S,T` have interfaces
`X→Y`, `Y→Z`, and `Z→W`, and first alpha-rename independent local owners so
that the three owner maps agree exactly on source-shared identities. Then
`Comp(Comp(R,S),T) = Comp(R,Comp(S,T))`: both contain precisely those
`(ρ,ω,X,W)` for which there are intermediate `Y,Z` satisfying `R`, `S`, and
`T` under restrictions of the same `ω`. Reassociation changes only the order
in which the same existential interface witnesses are introduced; it does
not give each subcomputation an independent type/family assignment.

If finite presentations carry formulas `K_R,K_S,K_T` with incidence maps,
their composite retains the conjunction
`K_R(ω|Ω_R) ∧ K_S(ω|Ω_S) ∧ K_T(ω|Ω_T)` and the induced incidence to all
dependent output views. Reassociation can regroup this conjunction but cannot
project a formula away merely because an intermediate row no longer mentions
its request. This is an exact carrier law; it does not prove that a chosen
finite syntax is closed under the existential interface projection or that
the source typing derivation generates these relations.

The execution-level counterpart is associativity of state-threading
continuation bind, up to observation bisimulation, provided each saved
continuation receives the appended bind and the live resumed environment and
state. For `Return`, both associations apply `F` then `G`; for `Request`, both
attach the same recursively associated continuation to the request; internal
steps preserve the bisimulation, including finite prefixes of nonreturning
paths. This law permits regrouping source sequencing and callback invocation.
It does not permit moving a shallow handler image across bind: the adjacent
counterexample shows that handler image is a transformation on the already
composed computation, not an algebra homomorphism.

**Injective reindexing commutes with static composition.** Let `θ` be a
sort-preserving capture-avoiding injection on the owned identities of `R` and
`S`, fixing the common outer assignment and mapping the shared owner
identities, intermediate interface, formula endpoints, and incidence by the
same map. Assume every relation atom and typed-family formula is equivariant
under `θ`, and the induced map is injective on complete intermediate
interfaces, including every request, owner, and boundary identity observed
there. Then:

```text
Tr_θ(Comp(R,S)) = Comp(Tr_θ(R),Tr_θ(S))
```

For either side, a witness consists of one intermediate interface `Y` and
restrictions of one joint identity assignment `ω`. The bijection from the
owned range of `θ` back to the original owned identities maps these witnesses
both ways. Relation atoms and symbolic typed-family formulas then have the
same satisfaction under the corresponding assignments; source-shared owner
groups remain shared, and independent groups remain apart. `K_R ∧ K_S` and its
incidence therefore transport together, even when a request in `Y` is later
filtered from the support view. This proves naturality of static sequencing
for fresh use and injective intrusion at the relation level. It does not
establish that a solver computes the transported formula, that `θ` preserves
source typing, or that a non-injective parent quotient preserves the fiber.

#### Formulation choice and semantic/bookkeeping boundary

There are three plausible presentations of this same design problem:

| Candidate presentation | Conceptual economy and composition | Principality and proof reuse |
|---|---|---|
| A separate selector/obligation rule at each source site (`Sel_s`, `Demand`, typed-family pair obligations, and route-transfer cases) | Easy to attach to current solver events, but duplicates the meaning of row comparison, callback invocation, handler residualization, and variable transport. A new source form tends to need another rule. | Local checks can be executable, but their joint solution relation and cross-site preservation must be reconstructed. Proofs do not compose automatically. |
| A ground may-support row plus a separate provenance/route analysis | Small support algebra and a finite least-support candidate; operational visibility remains explicit. | Support alone forgets valuation, result/request, and continuation correlations. Separate analyses need a proved coupling, and handler images need not distribute over row union. This can be a derived coarse solver view only when the coupling theorem holds. |
| One assignment-indexed relation over complete roots, typed-request fibers, source-binder sharing, and dynamic handler behavior | One relation composes source evaluation, callbacks, and handler transitions; row splitting/filtering and lifecycle maps are projections or images. | Preserves correlations needed for principality and reuses image/transport lemmas, but may not have an effective finite principal presentation. That is an open theorem, not a reason to add site-specific semantic rules. |

The third presentation is the preferred mathematical candidate because it
reuses composition and transport proofs while retaining the information the
other two presentations discard. This is a preference among research
formulations, not a claim that the relation is already sound, principal, or
implementable. A ground row or local obligation may still be used as a solver
presentation when it is proved to denote the corresponding relational image.

The semantic distinctions are source evaluation and value/computation
boundaries, typed request arguments and source-owned sharing, and dynamic
handler visibility. These affect which observations a program can produce.
By contrast, `Sel_s` alternatives, `Demand` labels, typed-family obligation
records, route ledgers, and explicit transport maps are candidate derivation
or bookkeeping forms. They may be useful proof witnesses, but do not create
additional source semantics. A typed-family invariant itself is semantic: its
formula and ownership remain in the solution relation; an obligation object
is only one way to present it. Likewise, handler visibility is semantic while
a route record is evidence that a transition respects it.

The proof direction is therefore from one source evaluation/handler relation
to its typed interface relation, then from that relation to any finite solver
presentation. Site-local lemmas may be derived from this path. If a proposed
special case cannot be derived, first test whether it identifies a genuine
source distinction or whether the common relation or its observation map is
missing information; do not promote the special case into a semantic
constructor solely to fit an Oracle fixture.

#### Case sequencing as relational composition

Write `Run_ν(e,η,s)` for the candidate source-level computation relation of
expression `e` under type assignment `ν`, value environment `η`, and dynamic
machine state `s`. Its result is a computation observation; first-class
thunk values carry a separate latent relation. This differs from the mono
evaluator's raw `eval_expr` value, where a runtime `Thunk` may represent
either a suspended value or a pending source computation. The candidate
source typing/elaboration relation must determine which interpretation
applies. Define state-threading continuation composition `R >>= F` by
appending `F(v,η',s')` only after `R` returns `(v,η',s')`; for a request,
compose `F` into its saved continuation so that it runs under the environment
and state produced when that continuation is resumed. Thus handler-frame
unwind/re-entry and visibility changes are threaded through composition
rather than freezing the initial activation. Prefixes of nonreturning behavior
remain observations and do not invent a result. A case context requires a
value for pattern matching. For a fixed source typing derivation assigning
its scrutinee boundary `(S,T)`—the scrutinee's source value shape and the
pattern matcher's required value shape—the candidate typed execution equation
is

```text
Run_ν(case e of arms,η,s) =
  Run_ν(e,η,s) >>= (λ(v,η₁,s₁).
    Adapt_ν(S,T,v) >>= (λ(v',η₂,s₂).
      Match(v',arms,η₂,s₂)))
```

When the source/target shapes are equivalent, `Adapt` is the identity clause;
when they differ, its common value/thunk relation determines whether to force
or preserve a delayed value. This refines the untyped sequencing shorthand:
`Run(e)` is composed with the boundary required by the typed consumer before
the already defined pattern-binding, guard, and body relation `Match`. The
candidate does not choose `(S,T)` from a weight or solver event. The source
typing/elaboration rule that supplies that boundary remains open, and no
successor semantics is approved by this equation alone.

`Match(v,arms,η,s')` tests patterns in source order using one pattern-binding
relation and extends `η` with successful bindings. Pattern binding includes
conditional field-default evaluation; a default request and its continuation
remain in the relation. For each matching pattern, it evaluates the guard,
if present, under the resulting environment and dynamic state; a false guard
continues with the next arm, and a true or absent guard evaluates that arm's
body. A guard request and its continuation remain in this same
state-threading relation. The source-order structure can be made explicit
without introducing a new semantic operation: let `BindPat_i` be the
source-machine pattern-binding relation for arm `i`, with outcomes
`NoMatch(η₁,s₁)` or `Matched(η₁,s₁)`, and let `Guard_i` be its ordinary
expression evaluation when present. Then the arm sequence is the following
recursive composition of those existing relations:

For one record field with subpattern `p` and default expression `e`, the
candidate binding relation is the corresponding presence split:

```text
BindField_{p,e}(r,η,s) =
  BindPat(p,v,η,s)                                      if field(r)=Present(v)
  Run_ν(e,η,s) >>= λ(v,η',s'). BindPat(p,v,η',s')       if field(r)=Missing
```

The second branch uses the same `>>=` as ordinary expression sequencing. If
`Run_ν(e)` yields a request, `>>=` attaches the remaining pattern binding to
that request's continuation; after resume it receives the resumed environment
and state. This is the candidate explanation for the frozen runtime's
`continue_value_as_bind` behavior. The row/effect view is projected from the
whole relation, so it includes default requests on missing-field paths without
adding a pattern-default effect rule or independently unioning support rows.
Any symbolic typed-family predicate on such a request remains in the composed
relation through that continuation; materializing the remaining row cannot
recreate it if it has been dropped.
This characterizes the frozen runtime at `a58eefc3`; the source typing rule
that selects the branch from record shape, and its symbolic field-presence
constraints, remain open.

```text
Match_i(v,η,s) =
  BindPat_i(v,η,s) >>= λoutcome.
    case outcome of
      NoMatch(η₁,s₁) -> Match_{i+1}(v,η₁,s₁)
      Matched(η₁,s₁) ->
        Guard_i(η₁,s₁) >>= λ(b,η₂,s₂).
          if b then Run_ν(Body_i,η₂,s₂)
          else Match_{i+1}(v,η₂,s₂)
```

For an arm without a guard, its guard relation returns `true` without a
transition. `BindPat_i` includes defaults only on the source machine's
missing-field path; defaults and guards that emit requests keep those
requests and their saved continuations in the composed relation. The terminal
case `Match_{n+1}` is the source machine's existing no-arm outcome; this
notation does not choose whether that outcome is an exception, failure, or
divergence. The equation is a sequencing decomposition, not an independent
effect rule for patterns or cases.

**Finite-arm trace preservation.** For a fixed finite arm list, induction on
`n-i` shows that every finite trace of `Match_i` is obtained through one of
the displayed relational branches: pattern-binding prefixes are followed by
the matched arm's guard/body, or by the next arm after mismatch/false guard.
The induction step uses the state-threaded `>>=` relation, so a request in a
pattern default or guard keeps its continuation and passes its resumed state
to the later match/body. Consequently, the request support of the ordered
match image includes all requests on these prefixes and selected suffixes.
This does not justify computing that support as an independent union of arm
rows; a later resumption can observe state changed by an earlier prefix. For
handler arms the terminal `NoArm` observation is then consumed by the enclosing
`Step_H` case, which forwards the original request with its handler-reentry
continuation.

For any observation relation `R`, define collected typed-request support at
fixed assignment `ν` by

```text
MayReq(R,ν) = ⋃ { typed_requests(τ) | (τ,o) ∈ R at assignment ν }
```

An earlier candidate claimed the following general support equation:

```text
MayReq(R >>= F,ν) = MayReq(R,ν)
  ∪ ⋃ { MayReq(F(r),ν) | r ∈ Ret*(R) }
```

Here `F(r)` receives the returned value, environment, and state. The equation
is **not established for the general stateful, multi-shot semantics**. Its
right side computes the resumptions of `R` independently of the effects of
`F`, while bind attaches `F` to each saved continuation. An effect in `F`
can therefore change the store or control state observed by a later resumption
of that continuation.

A distinguishing transition pattern is: `R` emits `q` with a reusable
continuation that reads cell `c`; at the initial state `c=0`, resuming it
returns without emitting `g`. The handler resumes it once, then resumes it
again, with no intervening mutation in the handler arm. Let `F` set `c:=1`
and emit no request from family `g` (any other direct request is immaterial).
In `R >>= F`, the first resumed
continuation runs `F` before returning to the handler; the second resumption
now sees `c=1` and may emit `g`. If `Ret*(R)` is computed from the initial
state without the `F` mutation, the displayed right side contains `q` but
misses `g`, while the composed relation contains `g`. This is a semantic
counterexample to the decomposition under that `Ret*` interpretation, not a
claim about a particular Oracle fixture.

The state-indexed witness can be written directly. Let `c∈{0,1}` and define

```text
k((),c=0) = Return(0,c=0)
k((),c=1) = Request(g, c=1, k_g)
R         = Request(q, c=0, k)
F(v,c)    = Return((), c:=1)
H_q(k')   = k'((),c=0); k'((),current_c)
```

Here the handler arm resumes the same continuation twice, and `k_g` may return
immediately. Without bind, both resumes of `k` see `c=0`, so
the standalone request tree has support `{q}` under this no-mutation handler
context; `F` by itself has empty support. With bind, the first `k'` call runs
`k` at `c=0` and then `F`, so the handler's second call runs `k` at `c=1` and
emits `g`. The composed pre-handler tree therefore has support `{q,g}` while
the independently computed support union is only `{q}`; after `H_q` consumes
the initial request, the residual support is `{g}`. This witness isolates the
failure to state feedback through a reused continuation; it does not depend on
typed-row matching or handler weight routing.

The frozen runtime has the relevant interaction shape: `continue_with_rc`
resumes the saved request through the same mutable `Runtime` before running
the appended continuation, and `ExprKind::RefSet` invokes the reference's
`update_effect` before completing the assignment
(`main` at `a58eefc3`, `crates/mono-runtime/src/runtime/thunk.rs` and
`runtime/eval.rs`). This is characterization evidence that the stateful
pattern is reachable in the runtime model; it does not prove a typed source
program realizing the exact `q`/`g` witness or any Oracle mismatch.

The sound general statement is only that support is projected from the
complete composed relation. The displayed equation can be recovered under
an additional resumption-stability condition: every store/control state
change introduced by `F` must leave the request support of all later `R`
resumptions unchanged, or `Ret*` must already quantify over a proved
F-closed set of such states. Neither condition is established for Yulang.
At the complete-interface level, composition still shares `ν`, source-owned
identities, and dependent symbolic formulas. A formula remains in the
composed relation unless a retained proof establishes equivalence for every
dependent view; the failed support equation does not authorize projecting a
typed-family constraint after its last request was filtered away.

The operational composition must therefore act on the complete resumable
computation, not on two support sets. As a candidate presentation, view it as
the source machine's possibly infinite execution relation. Its observable
yield/terminal forms are `Request(q,c,k)` and `Return(v,c)`, where `c` is the
current machine configuration and a saved resumption `k` accepts the response
and re-entry configuration allowed by the source handler semantics. Internal
evaluation steps remain part of the execution relation, including infinite
silent behavior. `Prefix(τ,c)` is an observation of any finite typed-request
prefix before a return, not a terminal computation constructor; every
execution contributes all its finite-prefix observations. Continuation
substitution at the observable forms is:

```text
Return(v,c) >>= F       = F(v,c)
Request(q,c,k) >>= F    = Request(q,c, λr. k(r) >>= F)
```

Here `r` carries the permitted resumed value and live machine state. In
particular, the store is not rolled back to the state captured when `k` was
created; dynamic handler/frame re-entry follows the source resumption wrapper
inside `k`. Thus after a first resume runs `F` and changes a shared cell, a
second resume feeds the changed state back into the original continuation.
Internal steps are relayed without invoking `F`; at a return, the first law
invokes it, while at a request the second law attaches it to the resumed
continuation. A non-returning branch therefore keeps all of its finite-prefix
observations and never invokes `F`. The counterexample above is represented by
this substitution. Handlers inspect and transform the same execution relation,
and `MayReq` is projected from all resulting finite-prefix and return
observations. This avoids adding a stateful-bind exception to the effect
algebra: the algebra acts on resumable behavior, and separability of its
support is a theorem only under proven conditions. The candidate execution
relation and live-state argument remain unproved against Yulang's runtime and
typed-family transport.

The already introduced `Step_{H,κ,ρ}` relation can be presented as one
activation transformer on these resumable nodes. On `Return(v,c)`, it runs
the value arm after leaving activation `H`. On `Request(q,c,k)`, it evaluates
the source-ordered arm matching relation using exact operation identity and
`Visible(q,H,c)`. If an arm accepts, it runs outside `H` and receives the raw
`k`; the result is the arm computation composed with whatever it does to `k`.
If no arm accepts, the request is forwarded after unwinding `H`, and its
continuation is wrapped to re-enter the same activation before continuing
`H(k(r))` after resumption. Pattern failure and false guards try later arms;
effects from arm guards run under the outer active context. These are cases
of one `Step_H` image, not a separate row-subtraction or callback rule.

The request's family/argument formulas remain in `K`, with `D` updated to
the dependent arm, continuation, and root views even when a matched request
node is consumed. The handler choice uses operation and visibility
coordinates, while operation-signature and payload/result constraints restrict
the same solution relation before its output support is projected. Thus
handling a visible request can remove an immediate support fact while its
symbolic family condition remains live through a raw continuation or another
root. This is the node-level form of the existing `K,D` transport obligation;
it does not make family equality or handler visibility a row-set property.

Application and shallow catch use the same relational operations, without a
callback-specific effect selector. Under the frozen runtime contract's
call-by-value evaluation of callee and argument expressions, the candidate
application equation is:

```text
Run_ν(e₁ e₂,η,s) =
  Run_ν(e₁,η,s) >>= (λ(f,η₁,s₁).
    Run_ν(e₂,η₁,s₁) >>= (λ(x,η₂,s₂).
      ApplyValue_ν(f,x,η₂,s₂)))
```

`ApplyValue` is the application case of the same machine relation on already
evaluated values. It dispatches a closure by evaluating its body in the
captured environment and applies primitives by their source semantics. An
effect operation or saved continuation application returns a thunk value
whose latent relation remains unrun until a later force. A thunk used as
callee follows the machine's force transition before dispatch. Thus callee
and argument evaluation compose immediately, while a returned thunk's
requests remain latent. The Function row contract must bound requests at the
source-defined call boundary; this equation alone does not prove that typing
rule.

A shallow `catch` applies the handler transition relation to this complete
call computation. On return it selects the value arm; on a request it tests
operation identity and activation visibility, then either enters the matching
arm with the raw continuation or forwards the request with the handler
restored on resumption. Its effect is the support projection of that
relational image. Thus call followed by catch is composition followed by one
image; row inclusion, callback invocation, and handler residualization need
no independent source-site effect constructs. These are conditional
source-semantics candidates: the runtime contract fixes the observed
evaluation and force cases, but the source typing relation and its finite
principal presentation remain unproved.

The case relation's request support is the projection of its complete
state-threaded composition above, including the typed boundary before
matching. Requests from forcing, pattern defaults, guards, and selected bodies
therefore stay joined with the same saved continuations, state, and `K,D`
incidence. Do not split this into independent `MayReq` rows for the scrutinee,
adaptation, and arms: a multi-shot resumption can observe mutations made by an
earlier continuation of any of these components. The exact `file::load`
fixture shows that the frozen evaluator forces the case operand before
matching, while current mono emission omits an explicit `ForceThunk`; it is
characterization for the open source typing boundary, not a typing rule. This
complete relational image is the candidate semantic authority. A finite
principal presentation of it remains unproved.

There is a further source/inference gap for record-pattern defaults. The
frozen runtime evaluates a missing-field default during pattern binding, and
the source language report says pattern matching can therefore perform
effects. Frozen `case_type` calls `consume_expr_value` while binding defaults
but discards the returned effect; its aggregate contains only scrutinee,
guard, and body effects. The same pattern-binding relation must account for
defaults in the successor. Whether Oracle accepts an effectful-default program
and the final-acceptance impact are unverified; the current code is evidence
of a possible under-approximation, not yet an accepted-program counterexample.
Principality remains relative to the chosen expressible row abstraction.

#### Candidate Function contract over the same relation

The source-rule map found no authoritative effectful Function contract in Y3:
F5 defines only its closed pure subset, and the application/catch references
specify syntax without typing or evaluation rules. The callback upper-bound
meaning must therefore remain a successor conjecture until the source
computation relation is selected and reviewed.

A compact candidate gives ordinary Function types a relational reading. A
first formulation took `CallCfg` from call boundaries reached by the
surrounding program. That is too weak for a compositional function meaning:
an unused function would have no such boundaries and its contract could hold
vacuously. Instead, let `CallCfg_{ρ,ν}(f,x)` be the set of all complete machine
configurations in which source well-typed contexts may apply callable value
`f` to argument value `x`, including contexts not reached by the current
program. Admissibility is defined by source typing, the well-formed store,
the ordered active-handler stack, and the callee's captured boundary lineage;
it is not selected by an effect-row rule or restricted to observed call sites.
The surrounding evaluation relation determines which such configurations
are reachable in a particular program, but reachability does not define the
function contract. Equivalently, `CallCfg` is the projection of the ordinary
source evaluation relation over all well-typed evaluation contexts that place
`f x` at a call boundary, under every semantic environment for the context's
free variables. The context has two typed value holes for the callable and
argument; `f` and `x` are plugged directly into those holes, not introduced as
variables in the semantic environment. The environment ranges over the
context's other free variables, and it need not arise from a closed program
that happens to construct `f` and `x`. This is a logical-relations closure of
the ordinary typing and evaluation judgments, not a new source typing rule.
Keeping the tested values out of the context environment avoids the direct
circularity where defining `f ∈ ⟦A ->[E] B⟧` first requires that same fact to
admit the environment containing `f`. Make the projection explicit with the
derived notation `Γ ⊢ C : (A ->[E] B, A) ↝ T` for an ordinary source evaluation
context with those two typed value holes and result type `T`, and
`Env_ν(Γ)` for semantic environments of its other free variables. Then
`CallCfg_{ρ,ν}(f,x)` consists of the call-boundary configurations obtained by
plugging `f,x` into every such `C`, running it under every
`η ∈ Env_ν(Γ)`, and projecting each execution to its application transition.
This notation abbreviates ordinary context typing and machine execution; it
does not add a call-site rule. The exact judgment remains open until the
source typing and machine relations are fixed. Let
`Beh_{ρ,ν,c}(f,x)` be the source-defined relation of finite evaluation
observations from applying `f` to `x` at configuration `c`. These inputs matter:
the same closure or thunk can be called under different active handler stacks,
and its captured boundary lineage affects which later requests are visible
after resumption. The complete relation carries these call configurations and
the callee interface together; neither is reconstructed from a materialized
row. Each observation is a pair `(τ,o)`, where `τ` is a finite typed-request
prefix and `o` is either `Return(v)` for a completed call or `Prefix` when
evaluation has not yet returned. Include every finite prefix, including
prefixes of runs that eventually diverge, so an emitted request is still
checked when there is no return value. A returned value records its latent
interfaces. Whether delayed requests belong to `τ` or only to a returned
latent interface must follow the source thunk/force rules; `Beh` does not
assume that boundary. Write `supp_now(τ)` for the **typed-request** support
observed at the source-defined call boundary, retaining each family argument.
Then a candidate denotation is:

```text
f ∈ ⟦A ->[E] B⟧_{ρ,ν} iff
  ∀x ∈ ⟦A⟧_{ρ,ν}.
  ∀c ∈ CallCfg_{ρ,ν}(f,x).
  ∀(τ,o) ∈ Beh_{ρ,ν,c}(f,x).
    supp_now(τ) ⊆ TypedRow(E,ν) ∧
    (o = Return(v) ⇒ v ∈ ⟦B⟧_{ρ,ν})
```

#### Conditional callback-forwarding consequence

Under this candidate clause, an ordinary application cannot lose a request
already observed in its complete application behavior. Consider the frozen
source witness:

```yulang
pub act ask:
  pub get: () -> unit

pub call(f: () -> [ask] ()) = f()
pub invoke(): [] () = call(\() -> ask::get())
pub result = invoke()
```

Assume the source operation relation gives `ask::get()` a request observation,
the lambda's call behavior includes that observation, application composes the
callee/argument/callback relations, and no handler lies between the callback
request and the exported `invoke` observation. The Function clause requires
the behavior of calling the annotated callback to be included in its `[ask]`
row. Relational application then places that request in `call`'s immediate
behavior; the same composition places it in `invoke`'s behavior. Since
`TypedRow([],ν)` contains no `ask` request, `invoke : () -> [] ()` cannot
satisfy the clause. The proof uses the general application composition and
the typed-row inclusion premise; it adds no callback-specific selector and
does not depend on exact request multiplicity or continuation-use counts.

The frozen Oracle accepts this source and serializes `call`'s return effect as
empty even though both runtimes report the unhandled `ask` request. The
weighted source trace and exact acceptance delta are recorded in
`notes/progress/2026-09-30-intrusion-weight-routing-counterexample-search.md`.
This is a concrete conflict for the current callback routing path, not a proof
that every isolated `push_pops` operation is unsound. The successor behavior
in this candidate is to preserve the request through application and remove it
only through a handler image justified by the source transition relation.
Whether the candidate Function clause is the source language's chosen
well-typedness relation, and the completeness/principality of its finite
presentation, remain open.

##### Transparent composition cannot erase an emitted request

The callback consequence is an instance of a **first-request** lemma, not a
general monotonicity law for `MayReq`. If an execution of `R` emits `q` as its
first outward request, then no external resumption has occurred before `q`.
Under state-threaded bind, `R >>= F` preserves that request node and its prefix:
at a `Request(q,k)` node, bind produces `Request(q, λr. k(r) >>= F)`. Thus the
same execution of `R >>= F` emits its first outward request `q`.

The first-request condition is essential. The earlier stateful multi-shot
counterexample in “Case sequencing as relational composition” shows why the
unrestricted statement is false: a request `q` reachable only after a prior
resume can disappear when the first resumed return runs `F`, mutates shared
state, and changes what the second resume observes. Accordingly, the following
is **not** a valid general law:

```text
MayReq(R,ν) ⊆ MayReq(R >>= F,ν)
```

The first-request lemma uses one fixed assignment and one concrete execution
prefix; it neither decomposes support into independent row unions nor says
anything about later requests reached through resumed continuations. For the
annotated `ask` witness above, the frozen mono dump resolves the emitted
runtime boundary: the generated `call` has an adapter from a source return of
`thunk[[ask],unit]` to target return `unit`; its result adaptation forces the
thunk before `call` returns. Thus `ask` is an outward first request rather
than only a latent request after that boundary. The pure callee and argument
stages add no earlier request, and no handler transition consumes it. A
Function row that bounds this observed behavior must contain `ask`; the frozen
empty row does not. The exact artifact and runtime contract evidence are in
`notes/progress/2026-09-30-intrusion-weight-routing-counterexample-search.md`,
“Force point in emitted mono code.” The remaining condition is the successor
source judgment: it must derive this call/result boundary compositionally and
prove generated adapters simulate it. The counterexample therefore establishes
an Oracle runtime/scheme conflict, while the candidate typing contradiction
remains conditional on source boundary adequacy. This is still specific to the
first-request premise, not a general callback-effect rule.

Symbolic typed-family preservation is a separate relation-composition
obligation, not a consequence of the operational prefix lemma. For a request
with argument term `a` under source-owned binder `g`, require the composite
presentation to retain `K(ν,g,a)` and transport its incidence to exactly the
retained views that depend on it. This follows conditionally when complete
interface composition conjoins component predicates under the same assignment
and unions their dependency maps; the prefix proof alone says nothing about
`K,D`. Filtering or a handler may remove immediate support through its
relational image, and may remove `K` only after proving equivalence for every
remaining dependent view.

Given that presentation premise, capture-avoiding generalization and use-site
renaming transport the first-request witness together with the owner, formula,
and incidence maps. Injective intrusion has the same reindexing property. A
non-injective type-parent quotient still needs the separate quotient/fiber
theorem; prefix preservation does not justify it. The first-request result
uses only ordinary computation composition, with no weight-routing or
callback-site semantic rule. It does not establish the source Function
contract, callback behavior latent behind a thunk, or a finite principal
effect presentation.

Define semantic Function compatibility by inclusion between these denotations.
Application composes callee evaluation, argument evaluation, and `Beh`; a
surrounding handler acts on the resulting complete computation relation. A
finite structural rule can use the usual argument contravariance, result
covariance, and `RowSub(E_actual,E_formal,ν)` only when both interfaces are
compared over the same source-typed call configurations and the captured
visibility lineage is preserved for every admissible call configuration. For
each fixed call configuration, the direct
proof is: every value admitted by `A_formal` is admitted by `A_actual`; each
observed result in `B_actual` is
also in `B_formal`; and each actual request support admitted by
`E_actual` is admitted by `E_formal` through `RowSub`. Thus every behavior
satisfying the actual contract satisfies the formal one. It need not
characterize all denotationally included function
types: an empty formal argument domain or an effect bound containing requests
that the actual function never emits can make semantic inclusion hold without
componentwise `RowSub`. The converse needs a saturation/full-abstraction
theorem and is not claimed. This structural rule uses the same row relation
as other interface comparisons, not a callback-site relation. The same `ν`
and family formula remain shared with root values and operation payloads.

The contract predicate checks the return and request bounds but does not by
itself express a chosen correlation between a particular result and request
trace. `Beh` retains that pair for each callable; if an inference scheme must
retain a correlation beyond these independent bounds, it must remain in the
ambient complete `Rel_C` constraint relation rather than be rebuilt from
function-type marginals.

There are two formulations to compare. An explicit finite product rule can
state the sufficient variance premises directly; it may be easier to execute,
but each boundary must still be justified and the product can lose
value/request correlation. Denotational inclusion is more permissive and
compositional, but its exact decision procedure and finite principal
presentation may be unavailable. Choosing the structural rule trades that
precision for a simpler solver and requires a final-acceptance comparison on
any resulting rejection. The relational denotation remains the candidate
mathematical core, not an established successor rule. Its source meaning must
derive the admissible `CallCfg` configurations by source typing and the
machine's evaluation relation, and derive `supp_now`, delayed operations and
thunks, callback invocation, and nonreturning prefixes from that same
relation. The call-context admissibility judgment must be compositional and
must include well-formed counterfactual contexts, or the function contract
collapses back to whole-program reachability and loses its compositional
meaning. Its finite principal presentation remains open; neither Oracle
routing nor the pure F5 Function rule settles it.

The call-configuration domain itself has three candidate definitions:

| Domain | Soundness/compositionality | Principality and proof cost |
| --- | --- | --- |
| Call sites reached by the current program | Cheap projection, but an unused function has an empty domain and its arrow contract holds vacuously. It is not compositional under moving a definition to another client. | Easy to compute but fails to constrain exported function behavior; reject. |
| Every runtime-well-formed machine configuration | Program-independent and compositional, but may include stores and handler stacks no well-typed source context can construct. | Simple denotational domain in principle, yet can reject source-valid functions and destroy Oracle final-acceptance capability; no reason to prefer it without a source theorem. |
| Every well-typed evaluation context under every semantic environment for its free variables | Contextual and compositional across clients, excludes dynamically impossible states by source typing, and ranges over denotable values even when no closed source program constructs them. | Best semantic fit, but requires a precise environment relation and context-typing/evaluation closure plus an effective finite principal abstraction of behaviors. This is the current candidate, not a proved decision procedure. |

The preferred domain is therefore contextual rather than whole-program
reachable or all-machine-state. A proof must show that the context and
environment relations are defined independently of the candidate solver and
closed under evaluation-context composition. For every `f` and `x` in the
arrow's denotations, plugging them into the two typed holes of the immediate
application context must yield at least one call configuration; otherwise
vacuity can reappear through an empty context fiber. The exact environment
relation, context grammar, and typing closure remain open source-semantics
work. Ambient environments and stores can themselves contain aliases and
recursive callbacks, so the value/context relation may still need a guarded
or mutually defined logical relation. Any step index used to establish that
definition would be proof machinery, not an extra effect selector or source
construct; whether it preserves a finite principal presentation is open.

There is a small non-vacuity lemma once the value-hole interface is fixed.
Assume a member of `⟦A ->[E] B⟧` is a runtime callable value with a well-formed
captured store, a member of `⟦A⟧` is a runtime value, and the source machine
has the ordinary call-by-value application transition for two value holes.
The empty caller context around `□_f □_x`, with the empty active-handler
stack, reaches the call boundary using the callable's captured store. Hence
`CallCfg(f,x)` contains at least that configuration, and the arrow clause
checks the call there. This proves only nonemptiness and the corresponding
empty-stack request/result bound; it does not prove that all typed contexts
are represented, that the captured store is well formed by the successor
typing relation, or that the contextual relation has a finite principal
presentation. An implementation whose `Apply` rule does not accept already-
evaluated value holes must supply the matching source context before using
this lemma.

#### Evaluation contexts and the frozen runtime contract

The syntax references do not define evaluation. Frozen Yulang2's reviewed
mono-VM and runtime-guard specifications define the intended runtime contract
that a successor must model when claiming compatibility (`a58eefc3`,
`spec/2026-06-13-mono-vm-contract.md`, §§ MakeThunk, ForceThunk, EffectOp,
Catch; `spec/2026-06-13-runtime-guard-markers.md`, §§ request visibility and
dynamic unwind). This is operational characterization, not a static typing
rule. The frozen evaluator has known deviations from this contract, recorded
below; they are not silently adopted as successor semantics.

Use one machine relation over configurations with an ordered activation stack
and request visibility evidence. At the semantic level, `Visible(q,h,κ)` is a
request-to-candidate-activation judgment: it determines whether this
particular activation may handle the request. Ordered search checks it for
each candidate handler while traversing `κ`; it must not first collapse the
stack to a global `Visible(q,κ)` fact and then treat that fact as permission
for every frame. Such an existential shortcut would let a request connected
only to an outer handler grant an inner same-family handler permission to
capture it, contrary to the caller-hygiene contract. This coordinate is
needed because it changes observable behavior. The runtime-guard contract
represents it with request-carried guard identities and the active stack, and defines
`add_id` coloring from an entry snapshot. The frozen evaluator also carries a
`handler_boundary` field. These concrete forms are implementation witnesses
for `Visible`, not separate inference rules or mathematical constructs. A
current-stack-only predicate is therefore incomplete. The specifications
give these cases:

The capture-contract behavior narrows what `Visible` may depend on. The frozen
source reference at `a58eefc3`, `web/docs/reference/effects.md`, says that a
concrete callback effect row grants matching-family visibility inside the
receiving function, while callback-origin effects without that contract remain
protected from an inner same-family handler. A focused nested-provider pair
also shows that an explicit grant on
the receiving function survives an intervening helper with a wildcard callback
row; changing only the receiver's row to wildcard moves handling to the outer
handler. The fixture and outputs are recorded in
`notes/progress/2026-09-30-intrusion-weight-routing-counterexample-search.md`.
With the concrete receiver row the inner handler returns `[2]`; changing only
that row to wildcard lets the outer handler return `[1]`. Thus
operation-family equality and the nearest active handler do not determine
visibility by themselves.

Three possible visibility carriers have different status:

| Candidate | Assessment |
| --- | --- |
| `Visible` from operation family and active stack alone | Rejected by the paired nested-provider observation: equal family and stack shape, different source capture contract, different handler result. |
| One transferable Boolean per family | Too coarse without scope and origin: it cannot state which request occurrence received the grant or whether a returned value may carry it beyond the receiver activation. It also risks collapsing absent, concrete, and wildcard annotation forms. |
| The complete typed request/interface relation with source-owner incidence and the active activation context | Preferred proof carrier: the source contract can constrain the same symbolic request relation, and `Visible` is a projection of that relation plus context. It is not yet defined by successor source typing, and finite principal presentation remains open. |

This is not a choice to copy Oracle weights. It is a consequence of the
observable capture-contract distinction in the source reference. Request
provenance and active handler identities must remain separate from type-family
identity, while route ledgers remain derivation evidence. The next semantic
obligation is to define how ordinary source typing assigns and scopes those
owner/incidence links for each supported annotation form, including helper
calls, closure escape, thunk force, generalization, and instantiation.

A candidate context shape, leaving the contract interpretation symbolic, is:

```text
κ = ordered active frames, each paired with its source-typed capture relation
Origin(q) = source-owned request occurrence plus its typed boundary incidence
Visible(q, h, κ) iff h is an active frame in κ, h covers q.operation, and
  the complete source relation connects Origin(q) to h's capture relation
```

The handler-relative form is required even before the boundary-composition
rule is selected. For `κ = [h_inner,h_outer]`, a request connected only to
`h_outer` must fail `Visible(q,h_inner,κ)` and may pass
`Visible(q,h_outer,κ)`. Exact operation-family equality and an existential
outer witness cannot transfer that connection to `h_inner`.

This formulation makes the required distinctions explicit without choosing a
weight algebra: the source transition determines how nested calls relate their
activation contexts; unwinding and resuming determine which context is active;
and a returned closure or thunk carries later re-entry lineage only when its
complete value interface entails that dependency. The user selected
preservation as the intended source semantics for a nested concrete receiver:
an enclosing capture entitlement remains derivable through the nested
receiver's complete call/adaptation transition unless an independently
defined source boundary invalidates it. No such invalidating boundary is
currently specified for this transition. This is a semantics decision, not
implementation approval, and its source/runtime simulation and soundness proof
remain open. `Capture` is not a Boolean copied onto a family: its relation
must retain the source occurrence, symbolic contract, and activation
incidence together. This context form is proof notation for the common
interface, not a new source construct, solver obligation, or implementation
data structure.

#### Capture grants as scoped context, not request flags

The closure-escape probe exposes the insufficiency of treating a capture grant
as a permanent property of an effect family or request. In the frozen Oracle,
a concrete `[choose]` callback contract can erase the returned closure's
`choose` effect;
the pure caller is accepted, but both runtimes report the request unhandled.
The direct-closure control retains the effect. The complete probe and its
compatibility impact are in
`notes/progress/2026-10-01-intrusion-coarse-effect-abstraction-candidate.md`,
“Frozen-Oracle closure-escape probe.” A sound successor must preserve the
returned closure's latent `choose` request. This rejects that Oracle
under-approximation; it does not decide whether a more precise successor can
still accept the outer handler through its scoped visibility relation.

The common representation is an ordered dynamic context plus the
activation-specific value-carried lineage required by the Yulang3 runtime
architecture. Transporting that lineage is mandatory; its source-level
eligibility meaning remains separate. In particular, carrying lineage does
not snapshot the live handler stack or decide which later handler may consume
an escaped request:

```text
enter boundary: extend the ordered context with its source-typed capture relation
run helper:     extend the context; retain enclosing capture relations
request search: unwind exited frames before testing an outer handler
resume:         restore the unwound frames around the saved continuation
return value:   remove exited handlers; preserve the value-carried lineage
                required by its complete source interface
```

This separates three facts that a family flag would conflate: the symbolic
capture contract, whether its activation is currently active, and whether a
returned function/thunk must restore that activation when later entered. The
concrete-versus-wildcard helper probe supports context extension; the shallow
request semantics supports unwind and resume; frozen guard-marker behavior
characterizes value-carried re-entry. The source typing rule for whether a
grant dependency escapes in a closure remains unproved. In particular, do not
drop the callback effect from the returned function merely because a capture
contract constrained behavior during the maker activation. The exact escape
and re-entry relation must keep the same type-family assignment and `K,D`
incidence through generalization and each fresh use.

#### Candidate and open boundary lifetime for callback capture contracts

The Authoritative runtime-hygiene contract requires fresh activation-specific
guard/provider identities to travel with closures, thunks, and continuations
and to be reinstalled on resume. That lineage transport is fixed independently
of source capture entitlement. A concrete callback contract supplies an
active context inherited by nested helper calls, so a wildcard helper cannot
erase an enclosing capture entitlement. The returned closure retains its
complete latent request interface, including symbolic family constraints;
subtracting emitted immediate support still requires the handler-image proof.

The remaining escape question is whether an active caller handler may consume
a request when a returned closure later runs. The callback contract on the
maker cannot simply be transferred to a new handler by family equality, but
that fact does not establish that every ordinary caller handler is ineligible.
The source relation must combine the request origin, required carried
lineage, current handler activation, exact operation coverage, and any
source-defined boundary conditions. Neither preserving the latent effect nor
transporting lineage alone proves the result.

This implements the selected reading of the source phrase “handlers inside the
receiving function may consume” the contracted family for nested calls while
the receiving activation and candidate handler remain active. It does not
settle which entitlement an escaped value carries after return. That separate
source question still concerns function return/unwind, closure escape/re-entry,
and saved-continuation resume; each must transport the request origin and
typed-family formula. The frozen marker implementation remains
characterization evidence, not authority for that escape rule.

The separate closure-effect soundness invariant is firmer: constructing
`\_ -> f()` emits no request, but the returned arrow retains the callback's
symbolic latent effect. The frozen Oracle accepts a pure caller while both
runtimes leave `choose::reject` unhandled. The lost latent effect is a
soundness conflict in the inferred Function interface; final caller
acceptance is a separate question because a precise caller handler image may
consume the request. The current coarse whole-scrutinee abstraction rejects
the pure result annotation in either eligibility branch, but that is an
abstraction limitation, not proof that all sound finite presentations must
reject it. Record the checker/runtime conflict without treating either
outcome as the successor rule.

The user's selected default is ordinary caller handling, conditional on the
ordinary current source relation deriving visibility for that particular
request and caller activation. The maker's callback contract does not transfer
to a fresh handler by family equality, and its continued runtime lineage is
not itself a grant or a mask. No independent source-language principle has
been identified that would make the maker boundary persistently mask later
handlers. A mask therefore has no place in the successor absent a new
source-level reason.

This is a choice of semantic direction, not a completed source theorem. The
common relation must still derive how the escaped request's origin and
lineage join a fresh caller handler under ordinary closure/application rules.
If it cannot, do not silently treat lineage as that join and do not infer a
mask from its failure. Return a concrete source-level counterexample for
reconsideration. Until that derivation exists, the ordinary-handling clause is
conditional and no pure caller result follows merely from the callback's
latent row.

The discriminators constrain that derivation. For an escaped callback, return
removes maker-local handler activations while preserving the closure's latent
request, origin, symbolic `K,D`, and required runtime lineage; invoking the
closure under a fresh handler uses only that handler's ordinary `Visible`
derivation and ordered search. A direct ordinary effectful closure must use
the same ordinary handler relation. A mixed-origin wrapper keeps separate
request origins and `K,D` even when requests share one typed family, so neither
origin lends the other a maker grant. A two-request shallow-resumption case
must route the raw suffix through the actual handler image rather than
subtracting the whole latent row after the first request. Every actually
selected arm remains subject to universal `OpCompat`; compatibility does not
alter runtime selection.

| Discriminator | Consequence of the selected default | Remaining proof obligation |
|---|---|---|
| Escaped callback under a fresh caller handler | Preserve latent request and lineage; allow handling only if ordinary current `Visible` and ordered search derive it | Derive the fresh-handler/source-origin join; maker grant alone proves neither eligibility nor ineligibility |
| Mixed-origin callback and caller thunk | Keep event origins and each symbolic `K,D` incidence distinct; family equality transfers nothing | Prove closure/Force/application transport in one valuation; the separate imported-Force A/B gate remains open |
| Ordinary effectful closure | Retain its latent effect and use the same ordinary handler relation | Prove the escaped case is a consequence of the same relation, not a callback-only rule |
| Repeated request with raw shallow resumption | A fresh handler may consume one request without erasing an unhandled suffix | Compute the complete handler image over reachable continuations |
| Ordered selection with typed incompatibility | Search selects by ordinary runtime/source order and visibility; an actually selected incompatible arm makes the typing derivation fail | Prove universal `OpCompat` over reachable selected events |

These cases reveal no source-level reason for a persistent maker-boundary
mask. They do not yet prove source adequacy, soundness of the full handler
image, or principality of its finite abstraction.

**Conditional ordinary-flow lemma for an escaped closure.** Let a closure `d`
be returned normally from receiver activation `r`, with body retaining a
callback value `f` and its latent request relation. Let a later ordinary
application of `d` occur while caller handler activation `h` is active in the
current machine context. Suppose that application exposes request event
`q[o]`, the request's origin-specific symbolic `K,D` remain in the same
assignment, `h` is still active and covers the exact operation, and the
ordinary source visibility relation has no intervening boundary that blocks
this event from reaching `h`. Then the ordinary `Run`/bind/application relation
propagates `q[o]` to the current ordered `Search_H`; if that search reaches and
selects `h`, `q[o]` is handled there subject to `OpCompat`.

The proof uses no maker grant. Normal return removes `r` and its handler
activations from the active context while retaining `d`'s latent request,
origin, `K,D`, and required value-carried runtime lineage. Later `ApplyValue`
evaluates the closure body in the then-current machine configuration; the
captured value environment does not restore the exited maker handler stack.
State-threaded bind transports the exposed request and its saved continuation
to the surrounding search. The source search then applies its usual
handler-relative visibility and ordered selection. A direct effectful
closure uses the same application and search steps. Mixed-origin bodies use
them per event, retaining distinct origins and `K,D`; sharing a family does
not transfer callback capture between events. Raw continuation suffixes still
need their own search derivations after a shallow arm exits.

This lemma is conditional at the exact point the existing draft leaves open:
the successor source relation must derive the ordinary outward-flow premise
for closure/application and determine whether any *currently active*
callback boundary blocks a particular event. That premise is a proof
coordinate of `Run`, its evaluation context, and `Visible`, not a new
callback-only selector or an inference obligation. Frozen public wording
supports capture for handlers inside a receiving function and hygiene against
inner handlers stealing a caller's effects; it states no persistent
post-return mask on a new outer caller. Accordingly, it gives no authority to
deny the ordinary-flow premise merely because `d` once crossed `r`. Runtime
lineage remains transported, but cannot substitute for either side of the
source visibility derivation. Current equations still admit the logical
independence model where this ordinary-flow premise is absent, so this is not
yet an unconditional derivation or a final soundness theorem.

The previous alternative table is retained as a compatibility record, with
the user's preference now fixed:

| Source rule for the caller's fresh handler | Result for the escaped request | Compatibility consequence |
|---|---|---|
| Ordinary caller handling when the current source relation makes that handler eligible | **Selected default.** The caller handler may consume the request after ordered matching; the maker's grant is not transferred | May retain Oracle final acceptance if the finite handler image proves a pure result; runtime route must agree with source semantics |
| A carried callback boundary masks this later handler | Rejected absent an independent source-language principle; the request would remain in the outward effect | Do not adopt to imitate frozen runtime routing |

Both rules preserve the closure's latent request and mandatory runtime
lineage. Fresh activation IDs, request origin, callback-contract identity,
symbolic `K,D`, and ordered handler stack remain distinct. The frozen checker
and runtime disagreement does not decide the source rule; the user's selected
default and the remaining proof boundary above do.

#### Nested concrete receiver: selected preserve clause and proof gate

The frozen both-concrete witness establishes a checker/runtime conflict:
Oracle accepts the program with `invoke` and `handle` reporting `ret_eff=Bot`,
then the runtime leaves `choose::get` unhandled after the nested `invoke`
adapter forces the callback result. The wildcard-helper and direct-receiver
controls distinguish this path, but do not decide its successor semantics.
The exact witness is recorded in
`notes/progress/2026-10-02-callback-scope-transition.md`. Do not reproduce
either the empty Oracle row or the runtime route as authority.

The user selected preservation as the intended source rule. State it within
the existing handler-relative visibility relation, not as a new grant store:

```text
Visible(q,h,κ)       NestedCallAdapt(b) keeps h active and carries q's same
                     source origin and capture incidence
───────────────────────────────────────────────────────────────────────────
Visible(q,h,push_inner(κ,b))
```

The stack is written in handler-search order, nearest activation first, so
`push_inner(κ,b)` prepends the newly entered nested receiver `b` to `κ`.

The premise ranges over the **complete** nested call transition: callee and
argument evaluation, argument adaptation, callback execution, result
adaptation, and any force required by the source boundary. It preserves the
whole visibility derivation, including ordered-context premises, not only
positive incidence facts. A source-defined event that exits `h`, changes the
request origin, or otherwise invalidates this exact entitlement is outside
the premise and must be justified by an independent source rule. No
same-family test alone invalidates or grants visibility. The selected rule
does not make an outer handler global: `Visible(q,h,push_inner(κ,b))` remains indexed by
that exact candidate handler `h`, exact request origin, active ordered
context, and operation identity. Handler coverage and selection remain
separate predicates of the complete transition.

This removes suspension/shadowing as an Oracle-matching candidate. It does
not follow merely from retaining a frame or from associativity of relational
composition; it is a chosen source clause whose preservation must be proved
against the operational contract. It adds no `Sel_s`, `Demand`, route, or
callback-specific obligation. The abstract context remains ordered; request
origin and typed-family formulas remain attached; handler subtraction remains
the image of the complete computation.

The proof gate must establish: (1) source/runtime simulation for the whole
`CallView`, including adaptation and force; (2) exact handler-relative
visibility without caller-owned same-family capture; (3) shallow handling
with the raw continuation outside the selected frame, including repeated
resumption and outer-frame behavior; (4) symbolic typed-family and `K,D`
transport at the same assignment through request selection, residualization,
generalization, fresh instantiation, and intrusion; (5) soundness and
principality for the selected finite abstraction; and (6) final-acceptance
comparison against the frozen Oracle. If proof yields a genuine
source-language counterexample to preservation, return the decision for
reconsideration instead of adding a site-specific exception. No implementation
is authorized by this source-semantics choice.

The caller-hygiene control is also part of that proof: a receiver's contract
must not grant eligibility to an unrelated caller-owned request solely because
its family matches. An independently eligible caller-owned request retains
its own derivation. Visibility must use the request's source-owned boundary incidence as
well as operation identity and ordered active frames. Any typed-family
predicate and incidence `K,D` must survive `CallView`, `Force`, handler image,
and SCC lifecycle transport at the same assignment; immediate support becoming
empty does not discharge that dependency.

**Conditional one-request source reduction under the selected rule.** For the
closed `handle`/`invoke` shape, let `h` be the catch activation inside
`handle`, `o` the callback-origin occurrence, and `b` the nested concrete
`invoke` receiver. Assume the source typing/evaluation relation establishes:

1. The exact callback contract derives handler-specific `Capture(o,h)` and
   initial `Visible(q,h,κ)` while `h` is active.
2. The complete source `CallView_ν(invoke,f)` includes the result adaptation
   and force before catch dispatch; the callback emits exactly one
   `choose::get` request `q`, whose origin remains `o` through those steps.
3. The nested call has no earlier eligible handler for `q`, and operation
   identity, payload, and result satisfy the selected arm's compatibility
   relation.
4. The arm invokes the raw continuation once with `unit`; the continuation
   lies outside `h` and returns through the remaining adapter with no further
   request. The value arm and all other parts of the complete computation emit
   no requests.

The selected preserve clause then transports `Visible(q,h,κ)` to
`Visible(q,h,push_inner(κ,b))`. Ordered search selects `h`, and the single raw
resumption returns normally with empty immediate request support in the whole
handler image. This is a conditional source-machine reduction, not evidence
that the current source typing rules derive premises 1–4. It is specific to a
request-free raw suffix; the generic `handle` callback may emit a second
request there, outside this shallow activation.

**Preservation and ordered search are separate lemmas.** Write
`Visible_ν(q,h,κ)` where typed request endpoints need to be explicit; the
shorter `Visible(q,h,κ)` notation fixes the same assignment as the enclosing
complete-interface relation. Let `Capture_ν(o,h)` denote the projection of
that source relation connecting origin `o` to the concrete contract at `h` for
the current request occurrence and callback invocation; it is not a separate
grant store or a global pair reusable by another request event. Under the
selected rule, a nested
`CallView` transition preserves `Capture_ν(o,h)` and `Visible_ν(q,h,κ)` when
it carries the same origin, keeps `h` active, and has no independent source
event that invalidates this entitlement. Its proof obligation factors over
the composition:

1. Callee/argument evaluation and entry of `b` preserve the source origin and
   push `b` at the front of the nearest-first context.
2. Argument adaptation and callback execution preserve the same `ν`, or apply
   one explicit equivariant transport to every request endpoint and its `K,D`
   incidence. A force emits the source occurrence carried by the delayed
   computation; it cannot manufacture callback ownership from family equality.
3. The underlying call and result adaptation satisfy the same transport
   premise. Activation lineage required by the runtime contract is restored
   on resume, while static family binders remain distinct from fresh dynamic
   identities.
4. Returning from `b` removes only `b`; it does not remove still-active `h`.

The source derivation that feeds this projection can be stated without a
callback-site selector. In one ordinary call derivation, take a receiver
argument occurrence `a` with concrete callback contract `E`, and a handler
activation `h` whose capture relation is attached by the ordinary source
context relation to that exact receiver activation and argument-contract
boundary. If the source evaluation/value relation attributes request `q[o]`
in the callback's latent call/force behavior to the computation supplied at
`a`, and the complete typed operation relation makes `q` compatible with `E`
at `ν`, the relation
projects `Capture_ν(o,h)`. The attribution is per request: merely forcing a
caller-owned thunk while executing the callback does not change its origin to
one owned by `a`, and `E` cannot grant capture to it by family match. This is
the ordinary callback contract plus source provenance projected into
`Capture`, not a new inference obligation or runtime grant store. The source
relation must not connect a nested receiver's handler to the outer receiver's
contract merely because that handler lies in the outer receiver's dynamic
extent; the nested handler needs its own source-derived contract connection.
The source evaluation/value relation still has to establish this ownership
premise for direct callback requests, forwarded thunks, wrappers, and mixed
computations. The frozen reference describes the callback contract but does
not prove this successor derivation.

**Open contract-scope question: imported `Force`.** The current constraints do
not decide whether the exact callback contract also connects an inherited
caller request when the callback explicitly forces a caller-owned thunk while
the receiver handler is active. Two source relations remain possible:

- The contract covers the complete executed callback computation. `Force`
  preserves the request's caller origin and may derive a separate capture
  incidence from the exact callback argument boundary, execution, active
  handler, and typed compatibility. This is not a grant from family equality.
- The contract covers requests owned by the supplied callback computation;
  a forced imported thunk keeps its caller boundary and receives no new
  incidence without a separate contract connection.

Both relations must retain the request's origin and its joint symbolic
`K,D` predicates. Under the first, a handler may consume the request and the
outer handler does not see it; under the second, the request remains in the
outward interface for an outer handler. The frozen source reference does not
select between them. Preserving an already-derived `Capture` through a nested
receiver and forbidding grants based only on family equality also do not
select between them: origin transport and capture-incidence creation are
separate relations. Until this scope is specified, the imported-thunk case is
a discriminator, not a proved counterexample or an established source rule.

The incidence must also be scoped more narrowly than a reusable pair
`Capture(origin,h)`: one source lineage can expose several dynamic request
events, and a connection justified by one callback execution must not
authorize another event outside that execution. In complete-interface
derivations, the shorthand `Capture_ν(o,h)` therefore means incidence for the
current request occurrence and its exact callback invocation/argument boundary
and handler activation. It is not a global capability indexed only by lineage
and handler. `Force` can preserve the lineage while creating a fresh dynamic
event; each such event needs its own source-flow and visibility derivation.
The finite inference presentation may quotient these execution witnesses only
after proving that the quotient preserves handler selection.

**Conditional Force/dispatch composition lemma (policy-parametric).** Fix one
assignment `ν` and one complete represented `Force` derivation. Each request
actually exposed on that derivation inherits the source computation lineage of
the delayed computation, while its typed endpoints and every dependent `K,D`
predicate are transported together at `ν`. A newly allocated dynamic event is
not identified with the inherited lineage or a previous event. Any capture
incidence for that event is a separate source-relation premise, scoped to the
exact invocation, argument contract, and handler activation. Candidate A may
add the imported-`Force` incidence rule; candidate B omits that rule. Neither
branch follows from origin transport, and under B no absence claim follows
unless all other incidence rules have been excluded.

If the resulting dispatch configuration derives `Visible_ν(q,h,κ)`, the arm
matches, and the ordinary ordered search selects `h` with no earlier selected
handler, the shallow transition dispatches that event to `h` and supplies its
raw continuation outside `h`. Any later request in the continuation requires
its own visibility derivation. This composes stipulated Force transport,
incidence, visibility, and dispatch relations; it does not derive their local
source rules, choose A/B, claim a request-free whole image, or prove handler
adequacy, principality, or finite inference acceptance.

The projection can be audited as one join in the common source relation: (i)
the request-origin/value-flow derivation connects `o` to the computation
supplied at `(r,a)`; (ii) the handler-installation/context derivation connects
`h` to that same receiver activation `r` and argument contract at `a`; and
(iii) the typed operation relation validates the request against `E` at `ν`.
These are proof coordinates of the ordinary call, value, and handler
transitions, not separate solver predicates. A nested call into receiver
`r₂` transports an already derived `Capture_ν(o,h)` for an outer handler that
remains active, but does not copy that incidence to a newly installed `h₂`;
`h₂` needs the corresponding join for `r₂` from its own source derivation.
For a closure that carries the callback computation beyond `r`, value flow
may transport its origin and symbolic incidence, but whether a later handler
activation can join them depends on the source-defined re-entry/value relation.
That escaped-closure case is still open and must not be inferred from lexical
nesting or family equality alone.

One part of the escape case follows from the existing activation-indexed
`Visible` judgment. `Capture_ν(o,h)` is an incidence fact; it does not keep
`h` active. If normal return exits the activation containing `h`, the return
transition removes `h` from `κ`, so `Visible_ν(q,h,κ)` no longer holds even if
a returned closure carries `o`, `K,D`, and boundary lineage. A saved
continuation that resumes across that exit may restore the same activation
`h` only through the source resumption transition. A later, independently
installed handler `h'` is a distinct activation and needs its own
source-derived capture connection; value-carried guard lineage alone does not
identify `h'` with `h`. Thus normal return/unwind ends the old handler's
eligibility through the active-context premise, without erasing the latent
request or its symbolic incidence. This does not settle whether that request
is visible to another active handler or whether a source value relation
transports additional re-entry lineage.

By composition of these stage relations, the complete `CallView` preserves
the handler-specific entitlement. This is conditional: the source
typing/evaluation rules must prove each stage premise, particularly the
adaptation-origin map and force placement. The user-selected source clause
rules out a negative premise that treats the mere presence of `b` as an
invalidator.

Ordered search then determines dispatch, not entitlement. Preservation
transports candidate-specific `Visible_ν(q,h_i,κ)` facts; it does not select a
handler or simplify the existing stateful ordered search. `Search_H` evaluates
source-ordered patterns and guards, including their state changes and effects;
a nearer arm that rejects may allow an outer arm to select, while a nearer
guard's effects run under the active outer context. Thus an outer `h_i` can
retain its visibility derivation while a nearer independently eligible `h_0`
is considered first. Only the existing `Search_H` relation determines which
handler actually selects. An unrelated same-family caller request has a
different origin and no `Capture_ν(o',h)` premise merely by sharing its family
head, so the preserve rule cannot grant it eligibility.

After `h_i` handles a request, its operation arm receives the raw continuation
outside that selected shallow frame. The preserve rule does not wrap this raw
continuation with `h_i`; a resumed suffix therefore cannot be re-caught by
that same selected activation. An independent outer activation may handle a
later request if its own visibility derivation and the ordered `Search_H`
permit it. Any forwarded continuation instead follows the source forwarding
rule and its specified frame re-entry. This separation prevents the
nested-call preservation clause from accidentally changing shallow-handler
semantics.

**Conditional frame-extension derivation.** Factor the relevant visibility
premises at assignment `ν` as the candidate handler's active identity, exact
operation compatibility, and the source incidence `Capture_ν(o,h)` from the
request's origin `o` to `h`'s concrete callback contract. This is a factorization
of the complete source judgment, not an alternative grant mechanism. The proof
below assumes this is exhaustive together with any other positive or negative
ordered-context premises of `Visible`, and that each such premise is preserved
by the corresponding stage. In particular, no independent source event in
this nested transition exits `h`, changes the request origin, or otherwise
invalidates this entitlement; the presence of `b` alone is not such an event.
For a nested transition from `κ` to `b::κ`, assume each stage either leaves `ν`, `q`,
`o`, `h`, and that incidence fixed, or applies one capture-avoiding transport
`θ` uniformly to the request endpoints, `K`, and `D`, while fixing imported
outer binders and preserving `h`'s activation. Assume the source incidence is
equivariant under that transport:

```text
Capture_ν(o,h)  iff  Capture_{θν}(θ·o,h)
```

Here `θ·o` keeps the source occurrence identity and transports only its
symbolic typed payload and incidence.

Then `Visible_ν(q,h,κ)` implies `Visible_{θν}(θ(q),h,b::κ)`. The proof is by
induction over the finite `CallView` stage sequence: active `h` remains in the
tail context, exact operation compatibility is preserved by the uniform map,
and the incidence premise follows from equivariance at each transported stage.
The identity-map case covers direct forwarding through callee/argument
evaluation; adapter, callback, and force stages require their actual source
rules to establish the equivariance premise. This proves context-extension
preservation conditional on those stage rules; it does not derive them from
runtime markers. If the full `Visible` judgment has further ordered-context
or negative premises, each must also be preserved by the corresponding stage;
the factorization above does not discharge any omitted premise.

The result is deliberately only an eligibility theorem. Existing stateful
`Search_H` still evaluates nearer arms in order against the evolving
configuration. If a nearer pattern or guard rejects, search continues with the
resulting state; a guard request is itself routed under the active outer
context. Preservation neither bypasses that transition nor makes `h` the
selected handler. If `Search_H` selects `h`, its ordinary selection premise
must include this transported `Visible` derivation. Once selected, the shallow
handler runs its arm outside `h` and passes the raw continuation; therefore
the frame-extension lemma no longer applies to that continuation unless a
separate source transition re-enters `h`. This establishes compatibility of
the preservation clause with ordered selection and shallow resumption, under
the stated source transition premises.

For a distinct caller-owned origin `o'`, frame extension cannot synthesize
`Capture_ν(o',h)`: the no-grant result follows from the origin-indexed premise,
not from family inequality. If one origin is reindexed, the same `θ` must map
its `K,D` incidence; independently freshening only the request endpoint would
invalidate the lemma's premise. This keeps the soundness argument local to
source eligibility. It is not yet a whole-language type-soundness theorem.
Nor does it prove principality: the least finite interface representing all
outputs of the stateful `Search_H` and raw continuation image is still open.
In particular, equal may-support can hide different resumed suffixes, so a
support-only transformer cannot justify residual subtraction.

**Callback-origin transport through `Adapt` and `CallView`.** Let `q` be an
individual dynamic request event, and let `origin(q)` identify the source
computation lineage that produced it, including the callback/thunk value
lineage carrying that computation. Repeated executions may produce distinct
dynamic events from one source-site template; a finite presentation may index
the template, but a site label is not an event or activation identity. The
origin-preservation premise for `B_{S,T}` is: a request exposed from an input
computation/thunk keeps that source lineage in the output observation. The
complete transport is split by identity kind: its type component maps the
typed endpoints and `K` formulas; its owned-occurrence component maps the
`D` incidences and any source/request-owner coordinates used to represent
that lineage; its compile-time boundary component maps handler binders.
None of these maps renames a concrete dynamic request-event ID or dynamic
activation ID. A later
execution may create a fresh event and activation while retaining the
transported source lineage; the source re-entry relation determines how that
lineage is installed in the live context. This callback transport is the
runtime-ID-fixing specialization of `Tr_θ`: `Θ_h` may reindex compile-time
handler-binder metadata and its references in the presentation of `κ`, while
acting identically on concrete activation IDs in a machine configuration.
Treating the request-origin pair as part of the request record gives the
corresponding bind-transport equation:

```text
Tr_θ(Request(q[o],c,k) >>= F)
  = Request(θ·q[θ·o], Tr_θ(c), λr'. Tr_θ(k(Tr_θ⁻¹(r')) >>= F))
```

The right side is the transported request with the transported continuation;
its concrete event ID is unchanged. Under equivariance of the source
`Capture` projection, the origin/handler witness maps with the owned-occurrence
and boundary components, and its `D` incidence maps alongside `K`. This is the
origin-labeled instance of the existing `Tr_θ`/bind commutation proof, so
injective freshening and injective intrusion renaming do not stale the capture
evidence. It does not derive the source origin labels, prove arbitrary
solution-fiber preservation, or justify a non-injective parent quotient that
merges distinct origins or boundaries.
Effects independently emitted by a conversion have their own source origins
whose eligibility must be derived from the full source relation; family match
alone does not grant them `Capture`.

Under this premise, the three thunk-shape clauses for `Adapt` preserve
callback-origin requests by structural composition. Identity adaptation
leaves the computation untouched. Thunk-to-computation adaptation forces the
input and then adapts its result, so an exposed request retains the forcee's
origin. Computation-to-thunk adaptation delays the same adaptation and carries
the latent origin and formula incidence in the returned value interface;
thunk-to-thunk adaptation delays `Force` followed by result adaptation and
carries both in that latent interface. Later force exposes the same source
lineage in a new dynamic event under the source-defined activation context and
required re-entry lineage; it does not itself allocate a fresh identity unless
that boundary requires one. This is a structural case analysis over the
displayed `Adapt` equations, conditional on the source `Force` and value-boundary relations
preserving their inherited interface coordinates. It does not transfer an
outer capture entitlement to effects newly produced by an unrelated conversion.

**Returned-thunk caller-hygiene discriminator.** The origin premise must be
tested on the value-flow edge, not inferred from family equality. Fix one
assignment and two same-family requests `q_cb` and `q_caller`. If a returned
thunk exposes a request with callback computation lineage `o_cb`, and the
source argument contract already derives `Capture(o_cb,h)`, then forcing that
thunk during nested result adaptation may preserve `Visible(q_cb,h,κ)` while
`h` stays active and the same transport maps its typed payload and `K,D`. If
the callback instead returns or forwards a caller-owned thunk with lineage
`o_caller`, `Capture(o_cb,h)` does not derive `Capture(o_caller,h)`; forcing
`q_caller` cannot borrow the callback's entitlement merely because its family
and payload match. An independent caller-side derivation may still make
`q_caller` visible. Lineage therefore belongs to each exposed request, not to
one whole thunk: a callback-created wrapper that forces a caller-owned thunk
must preserve the inner request's `o_caller`, and a thunk combining both
computations must retain both origins and their separate `K,D` incidences.
Which origins a source value/force relation exposes remains to be proved; this
discriminator does not define them or add a source-site rule.

This per-request stability is a consequence of the existing resumable bind
equation, once `q` is observed with its origin and typed incidence:

```text
Request(q[o], c, k) >>= F
  = Request(q[o], c, λr. k(r) >>= F)
```

Bind changes the saved continuation and leaves the already observed request
`q[o]` intact. Any request produced later by `k` or `F` keeps the origin
assigned by its own source computation. Thus a wrapper around `Force(u)` may
append callback work without relabeling an inner caller-owned request; mixed
request origins also remain separate. This proves only label stability in the
candidate computation relation. Source typing/evaluation must still establish
the request labels on thunk force, and handler dispatch must still apply the
raw-continuation cutoff before making any later visibility claim.

Substituting the three nonidentity thunk cases in `Adapt` yields the same
limited result without extra rules. For `Thunk(E,A) → T`, the forcee's already
observed requests keep their origins while result adaptation is appended to
their saved continuations; if a shallow handler handles one, that appended
work, if reached through raw resumption, runs outside that activation unless an
independent source transition re-enters it. For `S → Thunk(F,B)`,
adaptation returns a delayed value, so no request is dispatched merely by
wrapping it; its latent relation is exposed only at a later force, under that
force's source context. For `Thunk(E,A) → Thunk(F,B)`, the latent relation is
`Force(v) >>= Adapt(A,B)`: requests already emitted by `Force(v)` retain their
per-request origins, and requests emitted later by the result adaptation keep
their own source-derived origins. In all three cases, symbolic `K,D` transport
still depends on the common value-boundary/interface relation; bind preserves
an observed request but does not by itself prove the full incidence equation.

For a function adapter, the displayed `CallView` equation composes argument
adaptation, the underlying call, and result adaptation. For a callback-origin
request `q` already related to `h`'s contract (including one exposed by a force
in either conversion), the same origin/`K,D` transport premise composes across
those three relations. Conversion-generated requests require their own
source-derived incidence. For each such request, the previous lemma preserves
`Visible(q,h,κ)` up to the composed type transport only along the transition
prefix where `h` remains active and no independent source event invalidates
the entitlement. The user's selected rule says nested receiver entry alone is
not an invalidator; it does not keep `h` active after that same shallow handler
is selected. If `h` handles an earlier request in this `CallView`, its raw
continuation runs outside `h`, and a later suffix request receives no
preservation claim for that removed activation. A still-active independent
outer handler is governed by its own `Visible` derivation. If result
adaptation returns a still-delayed thunk and the enclosing source boundary
does not force it before leaving `h`, this proof establishes latent origin and
lineage transport only; it makes no claim that `h` remains eligible after
return. That is the separately open escaped-value question.

The frozen VM/runtime contract describes function-adapter adaptation as
including argument and result conversions, and locates thunk effects at
explicit force. Those statements characterize the composition shape and
runtime force placement, but do not prove the origin-preservation premise for
the successor `B` relation. That premise must be a theorem of the successor
source semantics, and its implementation must keep static source sites,
symbolic family binders, dynamic activation identities, and request events
distinct. This closes neither whole-language soundness nor principality.

The same derivation does not grant `h` eligibility for another caller-owned
`choose::get`. Such a request has a distinct origin `o'`; absent an independent
source incidence `Capture(o',h)`, the visibility premise fails even though its
family and operation labels match. A nearer handler is still examined first
by ordered search, and an independently eligible nearer handler may consume
the request. That affects which handler is selected on that path; it does not
erase `Capture(o,h)` or change the outer handler's source entitlement.

**Symbolic-family preservation at the handler step.** Suppose the input
relation contains a symbolic typed-family predicate `K(ν)` and incidence `D`
linking it to the callback input view. Every selected request contributes its
payload/result compatibility predicate at the same assignment `ν`. By the
definition of the whole handler image, an output pair `(ν,J)` is produced
from an input `(ν,I)` satisfying `K`; selection changes the request
observation, not `ν`. Therefore the output relation still satisfies `K(ν)`.
If `J` retains a dependent value, callback, continuation, or root view, `D`
must map that dependency to the output view. Empty immediate request support
alone is not grounds to project `K` or sever `D`. Generalization binds the
owned endpoint together with `K,D`; injective fresh instantiation renames all
of them together. Injective intrusion transports them by equivariance, while
non-injective parent intrusion remains valid only under the reviewed
observation-constant fiber condition. This proves the handler-step invariant
for the relational image, conditional on the source transition generating
the stated origin/payload facts; it does not prove the concrete solver keeps
that formula or that a non-injective parent map satisfies the quotient
condition.

Under premises 1–4, the successor source machine handles the request where the
frozen runtime reports it unhandled. The frozen `check` acceptance does not
establish successor final-check acceptance: finite presentation of the
conditional source relation remains open. If that presentation cannot derive
the pure result for this witness, record the exact acceptance loss before
considering any tradeoff. Generic handler principality also remains open: the
finite inference abstraction must cover every reachable output of the raw
continuation and retain a possible repeated request unless the complete
callback relation proves that suffix request-free. The full source/runtime
preservation proof and least finite output construction remain open.

**Closure construction keeps the latent effect independently.** In the ordinary
compositional fragment, if

```text
Γ, f : Unit -[E]-> Int ⊢ f() : Int ! E
```

then

```text
Γ, f : Unit -[E]-> Int ⊢ (λ(_:Unit). f()) : Unit -[E]-> Int ! ∅
```

The lambda construction emits no request; each later call executes `f()` and
therefore has the callback's complete latent request bound `E`. A capture
relation active while that later call runs may change which handler consumes
those requests, but cannot turn the returned arrow's latent `E` into `∅`.
For symbolic family arguments, the same owned identities and formula `K`
remain attached to `E` in the returned arrow; generalization and each fresh
instantiation transport them with one consistent binder map, separately from
activation lineage. This follows from relational call composition and the
ordinary lambda value rule. It is independent of callback-use counts and does
not require exact continuation-sensitive effects.

For a typed family argument, the same constraint must remain symbolic. If
`E` contains `F<α>` and the source family relation contributes `K_F(α)`, the
generalized returned-arrow view is the joint formula

```text
∀α. K_F(α) ∧ (Unit -[F<α>]-> Int)
```

up to the chosen constrained-scheme notation. Independent uses `u₁,u₂` apply
one capture-avoiding map each to the entire formula:
`K_F(αᵢ) ∧ (Unit -[F<αᵢ>]-> Int)`. They cannot freshen the row argument and
family constraint independently or recover `K_F` from a later concrete row.
An internal SCC use keeps the live `α`; an incoming use gets its own map. This
is exactly the generalization/instantiation transport law already required by
the coupled relation. The pure renaming case is established conditionally;
preservation under a non-injective intrusion parent quotient remains open.

This formulation is the selected source rule for nested concrete receiver
capture, and is preferable to a family/path-only selector or sticky grant bit
because its parts are relational composition, activation scope, and transport
of the complete interface. It does not by itself prove the one-step handler
semantics sound or principal, so it cannot yet justify inferred row removal.

Earlier review correctly observed that positive incidence and frame retention
alone cannot transport `Visible` if the judgment contains an unrelated
negative premise such as “no nested concrete receiver occurred.” The selected
source rule resolves that case: a nested concrete call/adaptation boundary
by itself does not invalidate an existing entitlement. Therefore the complete
`Visible` derivation must transport over the whole `CallView` whenever the same
origin/capture incidence is carried and `h` remains active. Its premises may
still require proof of exact origin, operation, active handler identity, and
runtime lineage; each must be preserved through argument adaptation, call,
result adaptation, and force. Ordered handler search remains separate: an
inner handler may be considered first, but that does not erase the outer
handler's entitlement. Only an independently specified source event that
actually exits `h`, changes the request origin, or otherwise invalidates that
entitlement can break this transport. No such nested-receiver invalidator is
currently defined. This is the selected semantic clause, not an inference
from frame retention or Oracle behavior.

**Conditional whole-image calculation for the concrete helper witness.** Let
`S` be the complete scrutinee relation for `catch invoke(f)`, including callee
and argument evaluation, both `CallView` adaptations, the underlying call,
callback invocation, and any force required before catch dispatch. Assume all
of the following in one source transition relation and at one symbolic
assignment:

1. The request originates from the exact `f` callback occurrence supplied to
   `handle`; the active catch belongs to that receiving function's
   `[choose]` capture contract; and its complete `Visible` derivation is
   preserved across the handler-free nested `invoke` boundary.
2. The complete `S` behavior has no unrelated requests or escaping values.
   Every reachable request path emits exactly `choose::get`; after the
   operation arm resumes its raw continuation once with `unit`, that suffix
   and the remaining arm computation return `unit` without another request.
   The value arm is also pure, and operation payload/result compatibility
   holds.
3. Every argument/result conversion and force that can expose this request
   occurs before the catch's dispatch completes. State, ordered frames, and
   all dependent symbolic predicates and incidence are retained under the
   same assignment.

Then the one handler image has empty immediate request support

```text
ReqSupport(H#_outer(S)) = ∅
```

for the immediate request observation: each visible request is selected, the
arm runs outside the shallow frame, and its single raw resumption exposes only
the stipulated request-free suffix. This does not claim that every output is
`Return(unit)`, that every execution terminates, or that the image is nonempty.
It is a conditional source-image corollary of relational composition and the
handler image, not a fixture-specific rule. It does not follow from incidence
retention alone, and it proves neither a finite presentation nor a pure
generalized scheme for `handle`.

That distinction is necessary for the final-acceptance gate. The generic
parameter type `() -> [choose] ()` admits callbacks with two sequential
`choose` requests; resuming the first raw continuation leaves the second
outside the shallow catch. A row-only input abstraction must therefore retain
`choose` in the residual support for the generic `handle` behavior. A more
precise application result may use additional callback/suffix correlation,
but a finite presentation must prove that it retains enough information
without requiring an unapproved linear or usage type system. Whether it can
preserve the exact witness's pure output in a context that requires purity, or
must record a final-acceptance difference, remains open. Symbolic `K,D` must
remain attached to all dependent output views even when this particular closed
operation has no family parameter and immediate support is empty.

- `Apply` evaluates callee and argument expressions before applying the
  resulting values. A `MakeThunk` expression captures a suspended computation
  and returns a thunk value; it does not evaluate that body.
- `ForceThunk` evaluates that suspended computation at the force site. An
  effect operation application constructs a thunk; forcing it emits the exact
  operation-path request. A thunk passed, stored, or returned without force
  therefore contributes a latent interface, not an immediate request.
- A catch value arm runs only after normal return. A matching, visible request
  enters its operation arm with the raw continuation, outside the matched
  shallow frame. An unmatched or invisible request is forwarded, with that
  frame re-applied when its continuation resumes. Eligibility uses exact
  operation identity, request-carried visibility evidence, and the
  activation's guard visibility; frame unwind and re-entry preserve the
  dynamic stack. The evaluator's additional `handler_boundary` field is
  implementation evidence, not part of this listed contract rule.
- A computed top-level root is evaluated once. A thunk-valued root is forced
  only at the explicit root boundary.

Consequently, `supp_now(τ)` in the Function candidate means typed requests
actually emitted before the source computation returns or yields its next
request under this machine. This boundary is semantic, not the runtime shape
tag: a `Thunk` used as the representation of a pending computation contributes
its requests to the current computation when the enclosing source context
demands its result, while a first-class thunk returned or passed onward carries
its behavior latently. The value/computation distinction must come from the
source typing and evaluation relation; inspecting a mono `Type::Thunk` alone
does not decide it. Callback application, handler transfer, and computation
demand are compositions of the same relation, rather than separate
callback/thunk effect rules. This leaves rows free to conservatively
over-approximate exact continuation-sensitive observations.

##### Typed value/computation boundary as one relation

The semantic core should be one typed boundary transition, not a source-site
`Demand` selector and not three unrelated effect rules. Let `B_{S,T}` be the
ordinary source typing/evaluation relation for transporting a value from
boundary type `S` to expected type `T`. It acts on complete interfaces, not
rows alone. For an input interface relation `R`, define its image by the same
relational-image pattern as handler transfer:

```text
Adapt#_{S,T}(R) = { (ν,J) |
    there are I, v, v' with (ν,I) ∈ R,
    v ∈ ⟦S⟧^val_ν, B_{S,T}(ν,I,v,v'), and
    J ∈ Obs_B(I,ν,v')
}
```

The input and output keep the same assignment `ν`; `I` and `J` include
request occurrences, continuation behavior, symbolic typed-family formulas,
and formula-to-view incidence. Thus `Adapt#` cannot validate a family
condition only after materializing its row. Formula and incidence transport
must be part of `B` and `Obs_B`; a support projection may follow the image but
cannot define it. This is a semantic contract for the candidate relation, not
yet a proved source rule or finite solver operation.

For a value `v`, write `Adapt_ν(S,T,v)` for the computation observed through
this boundary transition. Its thunk-sensitive behavior is characterized by a
disjoint outer-shape partition:

```text
Adapt_ν(S,T,v) = Return(v)                         when S ≈ T
Adapt_ν(Thunk(E,A), T, v) = Force(v) >>= Adapt_ν(A,T)
    when S ≉ T and T is not a Thunk
Adapt_ν(S, Thunk(F,B), v) = Return(Delay(Adapt_ν(S,B,v)))
    when S ≉ T and S is not a Thunk
Adapt_ν(Thunk(E,A), Thunk(F,B), v) =
    Return(Delay(Force(v) >>= Adapt_ν(A,B)))
    when S ≉ T
```

Here `≈` is the selected value boundary equivalence and has priority: when it
holds, the identity branch is chosen and none of the thunk-adaptation branches
apply. Otherwise the three thunk cases are mutually exclusive by their outer
source/target shapes. These equations are consequences that the source
typing/evaluation relation must establish for `B_{S,T}`; they do not define
independent row transformations. The clauses are available only when the
ordinary source type relation admits the payload/value conversion. In
particular, the target
latent contract must cover the *whole* delayed computation, including the
forced source computation and recursively adapted result, under the same `ν`
and typed-family ownership assignment. It cannot choose independent witnesses
for those parts. Ordinary non-thunk value conversions are other instances of
the same `B_{S,T}` relation and are not specified by this thunk-boundary
characterization.

The same boundary relation also gives the shape of a function adapter. For an
underlying function boundary `A_s → B_s` viewed through `A_t → B_t`, its
argument and result conversions compose around the ordinary call relation:

```text
CallView_ν(f,x) =
  Adapt_ν(A_t,A_s,x) >>= (λx_s.
    Call_ν(f,x_s) >>= (λy_s.
      Adapt_ν(B_s,B_t,y_s)))
```

Here `Call` is the source application computation relation on already adapted
values, and `>>=` is the existing state-threading relational composition; each
`Adapt` denotes the complete computation relation above, not a pure value
cast. Any dynamic visibility scope required by the source function-boundary
semantics surrounds the entire expression, including both conversions and the
call. The complete output interface must also carry whatever source-defined
activation lineage escapes on the returned value: a later force or call must
re-enter the required dynamic context, with fresh runtime identities kept
distinct from static type/family binders. That lineage belongs to the same
value/computation interface transported by `Adapt` and `Call`, not to a
post-hoc row annotation. This equation
derives callback argument/result transport from ordinary relational
composition and the same typed boundary used for thunks; it adds no
callback-specific row rule. It also identifies a key simulation obligation:
effects from argument adaptation, the call, and result adaptation must be
observed at the activation where that complete boundary executes. The frozen
Yulang2 `FunctionAdapter` contract at `a58eefc3`,
`spec/2026-06-13-mono-vm-contract.md`, § FunctionAdapter, has this shape, but
the guard-marker contract in `spec/2026-06-13-runtime-guard-markers.md` further
characterizes shape-directed argument/result marking and dynamic re-entry.
Both are characterization only; the successor source typing relation must
establish which source boundaries require this transport, its activation
lineage, and the symbolic family-incidence updates they induce.

The annotated `ask` callback is one concrete instance of this same equation:
the frozen mono dump shows the underlying `call` body returning
`Thunk([ask],unit)` while its adapter exposes return type `unit`. Thus
`B_s=Thunk([ask],unit)` and `B_t=unit`; the result leg of `CallView` is the
existing `Adapt(Thunk(E,A),T,v) = Force(v) >>= Adapt(A,T)` clause. For this
fixture the force first emits `ask`, so the first-request lemma carries that
request through the remaining result conversion before the adapted call
returns. This explains the observed mono boundary as a composition of the
ordinary typed boundary and call relation, without a callback-only effect
selector or an Oracle weight rule. It remains a runtime instance proof: the
successor source typing judgment must derive this boundary from its function
types and prove the same adapter simulation for every accepted conversion.

**Conditional adapter request theorem.** Choose one execution of the argument
adaptation and underlying call that emits no request and returns
`(v_s, η', s')`. Suppose `B_s = Thunk(E,A)`, `B_t = T` with `T` not a thunk
and `B_s ≉ B_t`; and suppose `Force(v_s)` has an execution from exactly
`(η', s')`, under the same `ν` and live activation, whose first outward
request is typed request `q`. The result leg of `CallView` is then
`Force(v_s) >>= Adapt(A,T,v)`. Stateful bind starts the result leg at that same
configuration, so the first-request lemma gives a corresponding execution of
the composition with the same first request `q`. In the absence of an
enclosing handler that consumes it, the complete adapter call's typed support
contains `q`; every target Function row that bounds this complete call via the
candidate typed-inclusion contract must include it. This is not a distributive
support equation: it uses one first-request trace witness and the defined bind
operation. The `call` / `ask::get()` dump meets these premises with
`A=T=unit` and `q=ask`.

For typed families, the operational premise alone is insufficient. The
complete interface image must additionally carry `K` and its incidence `D`
through `Force` and the later `Adapt`, under the same assignment and source
owner. This follows from the candidate composition rule only when the
transition presentation explicitly conjoins the predicates and transports
their dependencies to the views that remain. Thus the adapter theorem reuses
the common boundary relation and the symbolic lifecycle theorem; it does not
introduce a callback effect selector or silently discharge family invariance.

`Delay(C)` is a value whose force executes `C`; it does not run `C` while being
passed or returned. `Force(v)` exposes the thunk's complete computation
relation, including its typed-family formulas and resumptions. The clauses
therefore derive three behaviors from one typed boundary: run a source thunk
when a value is demanded, keep a value latent when a thunk is expected, or
adapt a thunk lazily to another thunk contract. They do not select different
row rules.

Sequencing `Adapt_ν` inside an active `Step_H` exposes its forced requests to
that activation; sequencing it after the catch exposes them outside. Returning
`Delay(C)` causes no request at either position until a later source context
forces it. Thus a latent row alone cannot choose the catch image, while the
boundary relation composes with the same handler image and `Comp` used
elsewhere. This is a candidate semantic interface derived from the frozen
`MakeThunk`/`ForceThunk` contract, not an approved source typing rule. The
source typing/elaboration relation must still show which `(S,T)` boundary
arises at each expression, and prove that its symbolic typed-family fiber
survives this adaptation, handler transfer, and every SCC lifecycle map.

**Conditional value-demand corollary.** Suppose the ordinary source typing
relation assigns an expression the boundary from source value shape `S` to a
consumer's required value shape `T`, then composes that boundary before the
consumer's eliminator. When `S = Thunk(E,A)`, `T` is not a thunk, and `S ≉ T`,
the same `Adapt` relation derives
`Force(v) >>= (λv'. Adapt_ν(A,T,v'))` before the eliminator. A case arm
matcher is one such eliminator if its source rule requires the scrutinee's
value; a function result boundary is another instance when its target result
type is `T`. Their
immediate support and handler image follow from composition at that context,
not from separate case or callback effect rules. If the source/target boundary
is equivalent, the identity `Adapt` clause applies. If it is not equivalent
and `T` has a thunk outer shape, the delayed thunk-target clause applies
instead.

In particular, if source typing assigns case scrutinee `e` the boundary
`(S,T)` before matching, its operational factorization is the ordinary
composition:

```text
Run_ν(case e of arms,η,s) =
  Run_ν(e,η,s) >>= (λ(v,η₁,s₁).
    Adapt_ν(S,T,v) >>= (λ(v',η₂,s₂).
      Match(v',arms,η₂,s₂)))
```

Here the typing premise gives `v'` the required scrutinee value type `T` for
the already defined ordered pattern/guard/body relation `Match`.
For `S=Thunk(E,A)`, non-thunk `T`, and `S ≉ T`, substituting the existing
`Adapt` clause places `Force(v)` before `Match`, with every request,
resumption, state change, and `K,D` dependency transported by the same binds.
This factorization is a corollary of the candidate `Adapt` and `Run(case)`
equations under the `(S,T)` premise; it does not derive that premise from
current Y3 typing or emitter behavior.

The conclusion is conditional on source typing deriving `(S,T)` and the
evaluation context placing `Adapt` before the consumer. It does not establish
that every case scrutinee or callback result has this shape. Frozen Y3
characterization sharpens the open premise: `case_type` splits a scrutinee
computation shape and includes its row, but does not record a consumer
boundary; the emitter retains the operand and the runtime forces it before
matching. The accepted `file::load` case is evidence that any successor source
rule must account for this observed demand if it is to preserve that final
acceptance. It does not make the runtime fallback an inference rule. The same
generic boundary must carry the complete symbolic family fiber and saved
lineage through the force and subsequent eliminator.

#### Live conflict: computation demand at a case scrutinee

There is now a concrete reachable conflict, not just a suspected evaluator
fallback. The successful frozen run fixture
`tests/yulang/regressions/runtime/file_native_invalid_path_typed_failure.yu`
cases directly on `std::io::file::file::load invalid`, and
`tests/yulang/cases.toml` expects `load-invalid`. In frozen `specialize2`,
`TaskSolver::case_type` splits the scrutinee's computation shape and includes
its effect, but records no consumer boundary for the scrutinee;
`specialize2/emit.rs` therefore emits the `Case` with that expression
unchanged. The evaluator forces the scrutinee before pattern matching. The
runtime contract instead requires `ForceThunk` to be explicit. Thus the
accepted source example depends on computation demand that is not represented
by an explicit force node in the emitted mono tree.

This evidence does not authorize a case-specific effect selector. The
candidate is the ordinary context closure of one source evaluation relation:
an evaluation context that needs a value composes the expression's computation
observations before matching or using its result; a context that transports a
first-class thunk retains its latent interface without running it. The same
context-composition relation governs case operands, reference operands, calls,
handler arms, and roots, with each context's value/computation boundary fixed
by source typing. Typed requests become immediate exactly when their
suspended computation is composed, retaining the same family arguments and
visibility lineage. This derives effect support from ordinary evaluation
composition, not from a site-specific `Demand` predicate.

The contract/evaluator mismatch remains open at the mono boundary: either
specialization must make this context composition explicit with
`ForceThunk`, or the runtime contract must recognize a typed context demand
that is currently implicit. The successor proof must establish which
simulation preserves final well-typed-program acceptance. The same reachability
audit found implicit force code for `RefSet` and some handler-result paths;
only the case path has a confirmed source run witness so far. It also found
that callee expressions receive a typed `Fun` consumer and normally get an
explicit boundary, so its fallback remains unproven. The semantic relation
checks `Visible(q,h,κ)` for each candidate handler during routing; the
evaluator's concrete guard fields and `handler_boundary` remain implementation
evidence, not additional inference rules. No soundness or final-acceptance
claim follows until these simulation obligations are closed.

This anchor does not decide which source expressions specialization must
lower to `MakeThunk` or `ForceThunk`, nor does it prove that Function effect
annotations denote upper bounds of the immediate observations. Those remain
static source-adequacy obligations. In particular, the inference relation
must predict every runtime thunk boundary without consulting the frozen
Oracle's weight routing.

#### Callback result at a shallow catch boundary

Frozen runtime source makes the missing boundary concrete. `eval_catch`
evaluates its body and dispatches `EvalResult::Value` to value arms and
`EvalResult::Request` to operation arms; it does not force a first-class thunk
value. The mono contract separately says `MakeThunk` suspends its body,
`ForceThunk` runs it, and an effect operation returns a thunk that emits its
request only when forced. Therefore the same callback's latent operation row
can lead to different catch images depending on the typed context:

```text
callback returns a thunk; catch transports it as a value
    => catch value arm; request remains latent
typed context forces the thunk before catch handles the result
    => request is emitted inside this catch activation
typed context forces the thunk after catch returns
    => request is emitted outside this catch activation
```

This is a source computation/value distinction, not a reason to add a
callback-specific selector or a new effect obligation. The source typing and
evaluation-context relation must determine where computation is composed and
where a thunk remains a value. `catchκ(e₁ e₂)` adequacy consequently needs one
context simulation that tracks the complete application result (including its
latent interface), inserts no demand by guessing from its row, and commutes
with `Step_H` only when the source context actually demands the thunk.

The frozen execution witness makes the simulation boundary concrete. In
`runtime.rs`, `MakeThunk` returns a thunk value without evaluating a suspended
body. An expression thunk stores that body, its captured environment, provider
environment, and hygiene-mark requirement; an immediate value may use the
`Value` thunk form. `eval_catch` keeps the catch active while evaluating its
body, then dispatches a returned `Value` to value arms and a returned request
to operation search. `ForceThunk` evaluates its operand and forces the thunk;
forcing an expression thunk evaluates its saved body under the captured
environment/provider context. A later request therefore enters the same
request/activation visibility relation as any other request at that force
boundary. A matched shallow arm gets the raw continuation after the catch has
unwound; a forwarded request wraps its continuation to re-enter the catch
after resumption. These are runtime transition facts, not source typing rules.
They motivate the obligation to show that the complete interface composes the
context's actual force with the proposed resumable computation relation, while
transporting saved value and activation lineage; a row annotation cannot
decide this boundary.

##### First-dispatch force/catch cut lemma (conditional)

Fix one complete type assignment `ν`, live state `(η,s)`, ordered activation
context `κ`, and a thunk value `d = Delay(C)` whose saved environment, provider
context, symbolic family formula/incidence `K,D`, and dormant activation
lineage are carried by the complete interface. Suppose forcing `d` from this
state has first outward event `q`. The ordinary source transition equations
distinguish the first dispatch and force point across these three context
traces:

```text
(a) Catch_κ(Return(d))
    first dispatch is Value(d); C has not executed before that dispatch.

(b) Catch_κ(Force(d) >>= F)
    first dispatch is Request(q) under the active κ;
    ordered Search_H uses exact operation identity, arm order/guards,
    and Visible(q,H,κ) as one eligibility premise for this candidate handler.

(c) Catch_κ(Return(d)) >>= (λd'. Force(d'))
    with a non-forcing value arm that returns d unchanged, and no saved
    lineage that re-enters κ during this later force:
    catch first dispatches Value(d) and unwinds κ; any first request q'
    from the subsequent Force(d) is outside κ.
```

Proof: `Return(d)` presents a value to `eval_catch`, whose first dispatch is
the value arm and does not step the suspended body before dispatch. In (b),
`Force(d)` steps the saved computation before catch dispatch; state-threaded
bind preserves its first request as the first event of the body, so catch
tests that request at `κ`. In (c), the premise makes the value arm return the
identical thunk without forcing; catch completes that value-arm computation
and leaves `κ` before the outer bind forces `d`. The value arm may change
state, so its later force may emit `q' ≠ q`; under the no-reentry premise,
that request is outside `κ`. These are cases of the same `Run`, bind, and
handler-image relations, not callback selectors or row-subtraction rules.

The lemma is only a local operational cut. It assumes the stated first-event
and value-arm premises; a forcing value arm does not satisfy case (c), while a
state-changing arm can change the event produced by the later force. Without
the no-reentry premise, the later routing context must be determined by the
saved-lineage transition itself. The lemma does not prove which source typing
contexts choose these boundaries, that `Visible` holds for a particular
callback, or that the frozen adapter behavior is the successor rule. It does
show why a latent row alone cannot choose handler subtraction: the same
`K,D`-indexed delayed computation can first be dispatched as a `Value` or
yield a `Request` before the catch returns, depending on ordinary context
composition. The source typing proof
must derive the boundary, and any finite presentation must transport its
symbolic family predicate, incidence, and saved lineage unchanged through the
corresponding relation image.

**Origin-indexed refinement of the force/catch cut.** Attach each request's
own origin to the observations of `C`, rather than one origin flag to `d`. In
(a), no request is observed yet, but the latent relation retains its individual
origins. In (b), if the first request is `q[o]`, force exposes that same request
origin before dispatch; visibility still requires the independent
`Capture(o,H)` and ordered `Visible(q[o],H,κ)` premises. Under the selected
nested-receiver rule, those premises persist through `b` only while `H` stays
active and the source transition preserves that origin and its `K,D` incidence.
In (c), a later event `q'[o']` keeps the origin assigned by the later source
operation, but `H` has already unwound; its origin alone cannot restore
visibility. Re-entry can change that conclusion only when the source
saved-lineage transition explicitly reinstalls the relevant activation. If a
shallow arm selected `H` before resumption, later raw-suffix requests are
outside `H` regardless of their origin, unless an independent source
transition explicitly re-enters that activation. This separates request
provenance from handler availability; the source rules and symbolic transport
premises remain open.

Textual nesting and exact operation path still do not prove that the request
is eligible for the active arm. Focused frozen-Oracle witnesses place the same
`choose::get` callback under a matching catch outside `call(...)`, or outside
a caller of `call`; both pass `check`, but both interpreter runs report an
unhandled request. The mono path carries
`add_id[1, choose, own, resume-own]`, consistent with the capture boundary
blocking the outer catches. A positive control puts the catch in the body of
the callback-receiving function,
`handle(f: () -> [choose] ()) = catch f(): ...`; that source passes `check`
and runs successfully. Its runtime trace shows the request's carried guard
listing the active handler boundary among `exposed_guard_ids`, with
`skipped=None`. This matches the frozen source contract: a concrete callback
capture row exposes the family to a handler inside the receiving function,
not to an outer caller merely because the operation path matches. Thus these
observations support keeping operation identity, call/result conversion, and
activation/lineage together in `Visible`; they do not establish a source typing
theorem or justify a callback-specific selector. The exact executable build
provenance is not reconstructed.
The source wording is `web/docs/reference/type-theory.md`, “What Effect
Annotations Mean”; the runtime capture and eligibility details are specified
in `spec/2026-06-13-runtime-guard-markers.md`.

The evidence is in the frozen checkout `a58eefc31`,
`crates/evidence-vm/src/runtime.rs` (`MakeThunk`, `ForceThunk`,
`force_thunk_result`, `eval_catch`, and shallow continuation handling),
`spec/2026-06-13-mono-vm-contract.md` § Catch/effect handler, and
`spec/2026-06-13-runtime-guard-markers.md`. It establishes runtime ordering
only. It does not establish that a successor source typing derivation gives
the callback the required thunk type, which source contexts insert the force,
or that specialization simulates every such accepted derivation.

The same simulation must transport dynamic visibility. Exact operation
identity alone does not imply that activation `κ` handles a request: the
frozen guard contract also compares request-carried guard lineage with the
active ordered frame stack, and forwarded resumptions restore the frame on
re-entry. A typed request may therefore be forwarded despite matching an arm
path. At fixed `ν`, the source-to-`Step_H` correspondence must preserve live
state, ordered frames, request visibility, raw versus wrapped continuations,
and the symbolic family predicate/incidence `K,D`. Rows and route records can
present this relation, but cannot replace that correspondence proof.

The handler image also cannot generally be pushed through source sequencing.
Let `H_q` consume a visible `q` request without resuming its continuation and
return a pure value; its value arm returns values unchanged. Let a distinct
`p` request be unmatched and forwarded by `H_q`. Set
`R = Request(p,(), λ_. Return(v))` and let
`F(v)=Request(q,(), λ_. Return(w))`, with `q` still visible to `H_q` after
re-entry. Compare observations under an outer context that resumes `p`. Then
source sequencing gives
`R >>= F = Request(p,(), λ_. Request(q,(), λ_. Return(w)))`. Applying the
whole handler image forwards `p` with re-entry; when resumed, `F` emits `q`
inside that re-entered activation, so `H_q(R >>= F)` consumes `q`. But
`H_q(R) >>= F` appends `F` after the forwarded `H_q(R)` result; after `p` is
resumed and the inner handler returns, `F` emits `q` outside `H_q`. Thus the
two computations have different outward `q` support. This follows directly
from the shallow raw/forwarded continuation clauses, not from weights or row
matching. It proves that handler image and continuation composition are not
freely distributive; the uniform rule is to compose the complete source
computation first, then take one handler image. A finite support projection
must be proved against that whole image. The example is an abstract-machine
calculation; source typing reachability and symbolic `K,D` presentation remain
separate obligations.

The frozen runtime contracts and `eval_catch` implementation establish these
operational distinctions only. They do not establish the source typing rule
that chooses each demand boundary, a source-level guard-lineage theorem, or a
finite principal interface formula. No candidate successor rule is approved
or implied here.

#### Closed callback/catch calculation

Fix an assignment `ν`, imports `ρ`, and activation `κ`. Let `γ^row_{ν,κ,ρ}(E)`
be the row-only concretization: all continuation-bearing computations allowed
by the typed row view at `ν` whose immediate request-family support is
contained in `E`. It retains the listed typed-request formulas but forgets
additional callback-body relations on continuation suffixes, so it can be
strictly broader than the complete callback relation. Write `supp_F(c)` for
the family projection of immediate requests. Define its best support transfer by
`H#^row_{κ,ρ}(E) = ⋃ { supp_F(H_κ(c)) | c ∈ γ^row_{ν,κ,ρ}(E) }`.
This is a projection of the relational image for this coarse abstraction; it
is not the complete-interface `H#` above.

Assume evaluating the callee and callback value is pure, and `call` invokes
that callback once. Its formal function view admits `F<a>`. The actual
callback produces `Request(op_F<a>,p,k)`, with family formula `K_F(a)` and
payload/result interfaces attached to that request occurrence. Ordinary
function-value compatibility relates the actual callback interface to the
formal interface; it is not a callback-specific selector. Under the candidate
meaning that a formal latent row is an upper bound on emitted typed requests,
the row projection of that compatibility is the same `RowSub` relation
defined above, `RowSub(R_actual,R_formal,ν)`. That equation is conditional on
the source meaning of Function effect annotations; it does not create a
separate callback rule. Evaluation of
`call(actual)` composes the callee, argument, and callback-body relations. The
complete scrutinee retains `K_F(a)`. For this single-family calculation,
assume every computation in that composed relation belongs to
`γ^row_{ν,κ,ρ}({F})`. This premise covers the callee and argument evaluation,
the call body, the callback body, and every continuation suffix; it rules out
an unaccounted `G` request from any of them. Thus the call's support is a
subset of `{F}`, not merely a support containing `F`.

For the non-resuming case, require that every typed `F` request represented by
`γ^row_{ν,κ,ρ}({F})` is eligible at `κ`, is covered by a matching arm, and
satisfies its family and payload/resumption typing relation. Require the
value arm and every matching operation arm to return an immediate pure base
value without invoking or exporting the raw continuation. Then a `Return`
uses the pure value arm; a request in the tree is handled at its first `F`,
and no continuation suffix is entered. Thus
`H#^row_{κ,ρ}({F}) = ∅`. This is a universal coverage condition on the
concretization, not coverage of only the callback's observed operation. The
complete output relation still records its returned value and all latent
views; the equality concerns immediate request support.

For the resuming case, assume the same typed and eligible coverage, and that
the arms produce no requests of their own apart from those exposed by invoking
the raw continuation; their final returned values are pure base values. Also
assume there is a computation in this row-only concretization
whose first `F` request reaches an arm execution that invokes its raw
continuation, and that continuation then produces a second `F` request. The
first is handled, but resuming the raw continuation exposes the second outside
this shallow activation. Hence `H#^row_{κ,ρ}({F}) = {F}`. This reachable
resumption witness is essential: if the complete
callback relation constrains its continuation to a pure suffix, the exact
complete-interface image may be empty. The row-only transfer is conservative
because its concretization forgets that restriction, not because continuation
usage is typed linearly.

In both cases, `K_F(a)` remains in the complete symbolic relation, including
when the immediate residual support is empty; only a proof that all dependent
output and future-use views are preserved may discharge it. For the fixed
assignment and finite support powerset, the displayed unions are the least
representable support results: each union contains every concrete handled
support, and any other sound row must contain each member of that union.
Hence these are principal in that ground row abstraction.
This calculation does not prove the source callback-compatibility rule,
universal handler coverage for arbitrary rows, or a finite principal symbolic
scheme for typed families and result correlations.

### Handler transfer as a relational image

Let `C_ρ(I,ν)` be the set of well-typed continuation-bearing computations
represented by a complete interface `I` under the owned-variable assignment
`ν` and fixed imports `ρ`. It includes the values, captured environments,
latent function/thunk behavior, and activation lineage needed to interpret
later calls and forces. Let `H_κ` be
the source shallow-handler transformation at activation context `κ`. The
context includes the active handler stack and the source-defined visibility
relation; it is not calculated from a family row alone. The typed transition
may be partial on arbitrary configurations. Source progress/type preservation
must establish the needed cases for well-typed source computations.

For an interface relation `R` over owned valuations and root interfaces,
define the relational image over the whole input relation and its concrete
fiber:

```text
C_ρ(R, ν) = ⋃ { C_ρ(I,ν) | (ν, I) ∈ R }

H#_κ(R) = { (ν, J) |
    there are I, c, c' with (ν, I) ∈ R, c ∈ C_ρ(I,ν),
    Step_{H,κ,ρ}(ν,I,c,c'), and J ∈ Obs_H(I, ν, c') }
```

Write
`Step_{H,κ,ρ} ⊆ { (ν,I,c,c') | c ∈ C_ρ(I,ν) }` for the declarative
shallow-handler step at the fixed activation, including operation identity,
family argument, payload/result, and activation eligibility premises. Then

```text
Total_H(R,ν) iff ∀I. (ν,I) ∈ R ⇒
  ∀c ∈ C_ρ(I,ν). ∃c'. Step_{H,κ,ρ}(ν,I,c,c')
```

and `H#_κ` is the image of this context-indexed relation followed by the
common observation map. `Total_H` is only a meta-level condition for the
fiber-domain lemma below; it is not a source judgment, scheme conjunct, solver
obligation, or handler-specific semantic construct. Failure of this sufficient
condition on a finite over-approximation does not by itself imply inadequacy:
the extra represented computations may be spurious. Do not enforce totality by
deleting valuations or symbolic constraints. A source distinction that cannot
be expressed by `Step_H` and ordinary typing premises would expose a missing
observable coordinate or refute this candidate's unification.

Support preservation is quantified over this whole image. It does not require
retaining every request in the input may-support minus selected operation
heads: an aborting handler may make a continuation suffix unreachable. Raw
resumption and arm execution may also expose requests that simple subtraction
misses. For each request emitted on an output path, the source transition must
account for it by consuming it, forwarding it, or continuing that execution;
support is projected after the image. A finite presentation is sound when it
covers those reachable outputs, not when it performs local row deletion.

Here the complete observation includes output values with their latent
interfaces, typed request facts, family-argument denotations, occurrence
ownership, and route lineage. The finite presentation is separate: if
`p=(V,M,Q,K,D)`, its handler transformation must carry every formula in `K`
through its endpoint substitution and map its incidence `D` to the dependent
output views. A formula may leave the new presentation only with proof that
its meaning is preserved for every dependent output view. The finite formula
for the relational image composes `K` with the ordinary typed transition
relation and projects the intermediate computation; it does not create a
handler-specific predicate store. Observing concrete `c'` alone cannot
reconstruct this presentation proof.

The relation keeps `ν` fixed during transfer, so this image cannot validate a
typed-family condition only after erasing its symbolic endpoints. The induced
support view is the may-row effect of the handler. No `Drop` operation is
part of this definition. Source typing constraints generated by ordinary
transition/type rules remain in `R` with their symbolic endpoints; totality
does not reconstruct, add, or erase them. The collecting support projection
below deliberately states only ground support soundness and leastness; it does
not prove that a finite presentation transports `K,D` correctly.

The handler image has a useful fiber-domain criterion. If each `I` in `R` has
a represented concrete computation and the handler plus symbolic observation
are total on those fibers, then:

```text
dom_ν(H#_κ(R)) = dom_ν(R)
```

For the forward inclusion, an element of `H#` supplies its input `(ν,I)` in
`R`. For the reverse inclusion, choose the represented computation guaranteed
by nonemptiness and apply the total transition and observation to obtain an
output at the same `ν`. Any legitimate assignment restriction belongs to the
ordinary source derivation that formed `R`; it cannot arise later because row
materialization or residual support dropped a symbolic formula. This equality
is conditional on totality; it is not obtained by filtering `R`.

The exact-fiber criterion is stronger than the direct acceptance-adequacy
test. Let `R_src` be the source-derivable relation and `R_abs` a finite
presentation whose concretization may over-approximate source computations.
Universal totality of `R_abs` may fail because an extra abstract computation
has no typed transition. For example, let
the source fiber contain only a request `F<int>` with an `int` payload, while
a support-only concretization also admits `F<bool>` with a `string` payload;
an arm safe for the source request can fail universal coverage of the extra
abstract request. This is an abstract countermodel, not a claimed Yulang
source program. It means the fiber-domain lemma is unavailable, but by itself
does not show acceptance loss. Final-acceptance adequacy is the direct output
inclusion below: every output of the source transition must remain represented
by the finite handler image. If lost typed/payload correlation makes that
inclusion fail, refine the interface or use a separately proved sound output
abstraction; do not filter the source fiber to force totality. Ground support
soundness alone is insufficient for this gate.

The precise requirement on a finite interface language can be stated without
choosing a handler-specific fallback. For a source fiber `Src(ν,O)`, let
`γ(A)` be the computations represented by finite input interface `A`, and
let `Out_H(Src(ν,O))` be the outputs of the declarative source transition.
An input presentation is adequate for this handler when

```text
Src(ν,O) ⊆ γ(A)                         (input soundness)
Out_H(Src(ν,O)) ⊆ γ_out(H#_κ(A))         (output soundness)
```

Final-acceptance capability requires that every well-typed source fiber have
at least one finite `A` satisfying these inclusions and a finite output
presentation denoting `H#_κ(A)`. Spurious represented computations do not
create a source rejection merely because their typed transition is undefined;
they may be omitted from the image, provided every actual source output stays
covered. Principality additionally requires the selected output to be least
among sound outputs expressible for that input fiber. This is the finite
presentation theorem: retain enough typed request, payload/result, and
continuation correlation to cover the source fiber's outputs. It adds no
source rule. If no such `A` exists in the chosen finite language, that
language does not meet the charter's final-acceptance target for that fiber.

**Conditional transfer theorem.** Let `SrcComp_H(ν,I)` be the well-typed
source computations exposed by interface `I`. Suppose (1) each such
computation is represented in `C_ρ(I,ν)`, and (2) every source shallow-handler
result on those computations has a corresponding `Step_{H,κ,ρ}` witness whose
observation is represented by `Obs_H`. Then `H#_κ(R)` is sound: every concrete
handled result represented on an input fiber is represented on the output
fiber. No totality premise is needed for spurious members of the finite
over-approximation. `Total_H` is only required for the separate exact-domain
lemma above. Among exact output relations over the chosen complete-interface
carrier, `H#_κ(R)` is the least image containing all `Step_{H,κ,ρ}` observations
of the represented input fiber: any relation containing those observations
must contain `H#_κ(R)`. This is leastness for that semantic transfer, not a
proof that the image has a finite formula, that a solver computes it, or that
the whole type inference system is principal. Finite-presentation `K,D`
transport is a separate open correctness lemma, not a semantic premise of the
image.

### Symbolic preservation at one shallow-handler step

The semantic handler image acts on observable relations. A compiler
presentation of that image must transport its formula `K` and incidence `D`
without adding another obligation kind. At presentation level, a source
handler transition partitions the
scrutinee's typed request facts into facts forwarded, facts selected by the
source eligibility rule, and facts whose route is not known. It then acts as
follows:

1. A forwarded fact is mapped to the forwarded occurrence, with its boundary
   lineage extended by the handler transition. Its family-argument formulas
   and incidence move with that occurrence.
2. Before a selected request fact leaves the residual support, apply the
   source operation-signature relation to the symbolic request arguments and
   the arm's symbolic payload/result types. Add the resulting formulas to the
   same `K`; map their incidence to the arm, continuation, and output views
   that depend on them. The original formulas attached to the request remain
   in `K` until a solver proof establishes a semantics-preserving discharge.
3. An unknown route is not selected for removal. Keep its request fact or a
   sound unknown-support view, and retain its `K,D` incidence.

Whenever a request is matched to an arm, the handler transition compares
their complete instances of the same source operation declaration. For path
`p`, write the declaration as

```text
op : ∀b̄. A -> [E] B
```

and let `F<ρ̄>` be its family projection, where `ρ̄` is the subtuple of
declaration binders used by the family. Let `Λ` name all effect
obligations/interfaces declared with the operation; this notation does not
classify any member as immediate, latent, or owned by a particular value.
For binder substitution `θ`, use:

```text
OpInst(p, θ) = (OpId(p), F<θ(ρ̄)>, Aθ, Bθ, Λθ)
```

for its exact operation identity, declared family projection, payload and
result types, and all declared effect obligations/interfaces. This tuple is
only a view of the declaration under one substitution; it is not a new source
construct or separate solver obligation. The request and arm may use distinct
capture-avoiding substitutions `θ` and `φ` for the same declaration.

Define one source-level compatibility relation
`OpCompat_ν(q,h)` between a typed request occurrence and an arm. Its
candidate premises are exact `OpId` agreement; the source-selected invariant
relation between `F<θ(ρ̄)>` and `F<φ(ρ̄)>`; safe transport of payload `Aθ` to
the arm's input `Aφ`; safe transport from the arm's supplied resume value `Bφ`
to the request continuation's input `Bθ`; and the source-defined transport of
the complete declared effect interfaces `Λθ,Λφ`. Family, value, and effect coordinates
belong to this one relation because they come from one operation declaration
and binder maps. A finite solver may present its denotation as several
formulas, but those formulas are projections of one `OpCompat` fact and must
share the same `θ`, `φ`, assignment `ν`, and incidence with the request, arm,
continuation, and output interfaces.

The first two value-transfer directions have a conditional safety
justification: a request supplies a value of `Aθ`, so the arm must accept it;
the arm resumes with `Bφ`, so the raw request continuation must accept that
value at `Bθ`. The shallow transition gives the arm the raw continuation, so
the resume direction follows from that boundary. The exact family relation,
runtime-compatible subtype/coercion relation, and ownership of `Λ` still
require source semantics. In particular, do not guess whether a member of
`Λθ` is immediate or latent: retain it on the complete operation instance
until the source transition identifies its owner. In `H#` over the typed
source relation, the handler-arm branch of `Step_{H,κ,ρ}` requires both an
`OpCompat` witness and the dynamic selection event. This restriction applies
to the typed image, not to the runtime search relation. The runtime search
still selects by path, visibility, and source order if an ill-typed program is
executed. If such a selected event lacks `OpCompat`, the program has no
well-typed derivation; the typed image does not reinterpret it as a forwarded
request. When the source search actually forwards, the request instance and
its constraints remain. The full source rule and principality of its finite
presentation remain open.

#### Static compatibility is not dynamic dispatch

Keep `OpCompat` out of the runtime selector. Selection is an observation of
one ordered source handler-search execution over complete machine
configurations. That search includes the active stack, exact operation path,
visibility, source-order pattern/guard evaluation, their state changes and
effects, and any suspended search continuation. Write
`Search_H(κ,C,q) ⇓ Select(h,a,C')` only as notation for a search derivation
that actually reaches arm `a` at activation `h` from configuration `C` in
result configuration `C'`. It is not computed by testing every activation
independently against the same initial state. In the pure direct fragment,
nearest-eligible selection is a consequence of this search; for effectful
prefixes, state and pending search flow through its transitions. Once the
search selects `(h,a)`, the shallow arm receives the payload and raw
continuation. If the search forwards the request, the active handler remains
around the suffix. Family arguments do not create different runtime operation
identities.

Static typing has a separate preservation obligation: every arm actually
selected in a reachable well-typed source execution must satisfy
`OpCompat_ν(q,a)`. In trace notation:

```text
WellTyped_ν(C) ∧ SearchTrace_H(κ,C,q) contains Select(h,a,q,C')
  ⇒ OpCompat_ν(q,a)
```

`SearchTrace` is a trace of the one ordered search relation, so it includes
requests emitted by pattern/default/guard prefixes and resumes the pending
search only through their actual continuations. Each `Select` event names the
particular request it consumes; requests emitted during search have their own
request and selection events. The implication ranges over selected events
only: a shadowed outer arm imposes no condition unless search reaches it. This
is the ordinary type/handler preservation theorem, not a second dispatch test.
A failed compatibility premise rejects the program at
typing; it does not change a dynamic path match into forwarding. In the frozen
`ask<bool>`/`ask<int>` witness, if the successor source rule connects the
actual and formal callback rows, the selected arm cannot safely resume the
raw continuation at `bool` with an `int`. That conditional application of the
general preservation premise explains the concrete wrong Boolean result; it
does not prove the still-open callback row rule.

The quantifier is universal over reachable search events, not existential over
the successful branches of an inference formula. Define
`ReachSel_H(ν,I,q,a)` by existence of a source computation represented by the
fiber `(ν,I)` and an actual ordered search trace selecting arm `a` for request
`q`. Admissibility requires:

```text
∀ν,I,q,a. (ν,I) ∈ Rel_C ∧ ReachSel_H(ν,I,q,a)
          ⇒ OpCompat_ν(q,a)
```

Thus a request that can be forwarded on one execution and selected on another
must satisfy compatibility on every execution that selects it. An incompatible
selected event cannot be removed from the handler image while a compatible or
forwarding alternative keeps the disjunction satisfiable. Doing so would turn
an ill-typed branch into an apparently well-typed residual.

For an unknown visibility or incomplete search path, the finite inference
presentation cannot establish a unique `Select` observation. A sound image
must retain the possible forwarded request and cover every possible selected
arm result. It must also preserve the universal admissibility condition above;
keeping the request is not a claim that it is the whole image, and retaining
only compatible arm outputs is not sound. A type-compatible arm by itself does
not prove selection or coverage. The finite presentation must distinguish
actual reachable selected events from merely possible events introduced by a
coarse abstraction: it may not constrain a valuation because of a spurious
route, nor accept by dropping a reachable incompatible route. If the chosen
finite abstraction cannot make that distinction while remaining terminating
and principal, it has not met the source acceptance gate. The full search
relation for callbacks, adapters, effectful guards, and escaping values
remains open and must be derived from source boundary semantics.

The family predicate alone is insufficient even in a closed point case. Let
`F<>` have no family arguments and let the request payload be `Bool`, while
the arm expects `Int`. `family_relation(F<>,F<>)` is vacuously true, but no
runtime-safe `Bool <: Int` payload transfer exists in the ordinary disjoint
base-type fragment. The pair must therefore fail the complete
typed transition relation;
support-head equality cannot justify consuming it. This
tests the complete operation relation: payload/result behavior is already
part of `OpCompat`, not a new family-specific selector.

For any capture-avoiding type substitution `θ`, formula transport is
structural: `K_θ = θ(K)` and the same occurrence/owner map is applied to `D`.
If formula satisfaction is equivariant under type substitution, then
`ν' ⊨ θ(K)` exactly when the induced assignment `θ*ν'` satisfies `K`. This
proves substitution does not silently discard a symbolic family condition.
It is conditional on the chosen denotation of typed family arguments,
including the shared-witness behavior for interval-valued arguments; the
point-valued mutual-subtype shorthand alone is insufficient for that case.

The same transport obligation applies later: solving substitutes endpoints;
residualization changes request views only after their formulas and incidence
are carried; generalization quantifies locally owned endpoints with the
constraint; each use freshens endpoints, occurrence identities, and incidence
with one consistent map; intrusion applies its type-parent map to endpoints
and its boundary map to lineage. This is a formula-transport lemma, not the
fiber-preservation theorem for generalization or non-injective intrusion.
Those lifecycle theorems must still prove that the transformed relation has
the same observable solutions and independent-use behavior.

#### Conditional handler equivariance under injective transport

There is a useful local theorem for generalization freshening and injective
intrusion. Let `θ=(P_t,P_r,M,Θ_h)` be injective, capture-avoiding maps on
owned type identities, row binders, request/owner occurrences, and handler
identities. It fixes outer anchors, family and operation identities, and
preserves the order of every active handler frame. Let `Tr_θ` apply these maps
to the complete request relation, its symbolic formulas, payload/result
interfaces, and boundary lineage. Assume the source shallow transition
inspects only the fixed family/operation labels, type denotations, and
visibility induced by the ordered frame identities, and that all three
interpretations are equivariant under `θ`. Then:

```text
Tr_θ(H_κ(I)) = H_{Θ_h(κ)}(Tr_θ(I))
```

The equality is up to the same bijection `M` on produced request and proof
occurrences. For a forwarded request, both sides retain its label and map its
lineage through the corresponding frame. For a matched request, label and
operation tests are fixed, invariant argument and operation-signature
relations are preserved by `P_t`, and the arm/continuation transfer is
renamed by the same map. These cases establish one-step equivariance of the
small-step handler relation. Induction on finite transition prefixes gives
the equation for every finite observation, including arm-emitted requests
and resumed raw continuations. Taking may-support projections preserves this
equality.

This theorem transports the full activation stack; it never commutes, erases,
splits, or transfers a push/pop weight. It consequently supports freshening
and injective parent renaming when those maps preserve all relevant identities.
It does not prove solver solution-fiber preservation for arbitrary
substitutions, intrusion quotients that merge boundary/occurrence identities,
or handlers whose eligibility semantics distinguishes untransported dynamic
identities. The latter quotient cases require their own observational
preservation theorem.

#### Injective transport commutes with resumable bind

The same injective transport also commutes with the stateful continuation
substitution above. Let `θ` be capture-avoiding on the complete static
identity set used by one component: type and row binders, request/owner
occurrences, and static boundary identities. It fixes rigid imports and
operation labels and maps ordered boundary stacks to ordered stacks. Let
`Tr_θ` transport typed values, request arguments, symbolic formulas, their
incidence, and boundary lineage while preserving the live store and the
operational behavior of the machine state. For a continuation `F`, define its
transported form on the image of `Tr_θ` by

```text
F_θ(r') = Tr_θ(F(Tr_θ⁻¹(r')))
```

Then the candidate resumable-execution bind satisfies

```text
Tr_θ(T >>= F) = Tr_θ(T) >>= F_θ
```

Proof is by coinduction on the execution relation. For `Return(v,c)`, both
sides reduce to `Tr_θ(F(v,c))`. For `Request(q,c,k)`, both sides retain the
transported request and attach the continuation
`λr'. Tr_θ(k(Tr_θ⁻¹(r')) >>= F)`; the induction hypothesis rewrites this to
`λr'. Tr_θ(k(Tr_θ⁻¹(r'))) >>= F_θ`. For each finite `Prefix` observation,
both sides retain the transported prefix before any return. If execution
diverges, the equality holds for every finite-prefix observation of that
branch. An internal machine step is preserved by the assumption that `Tr_θ`
preserves operational behavior; it invokes no `F` on either side. Since
`Tr_θ` also maps every `K` formula and its incidence, the equality transports
typed-family constraints through each request and every resumed suffix
without recreating them from support.

This is an equivariance lemma for capture-avoiding generalization freshening
and injective intrusion. Combined with the preceding handler equivariance, it
transports the whole `Handle_H(T >>= F)` image when `Visible` and the source
operation relation are equivariant under the same map. It does not validate
the withdrawn independent-support decomposition, and it says nothing about a
non-injective parent quotient or solution-fiber completeness of a solver.

**Conditional closure-value transport.** Let a source closure value consist
of its code, captured lexical environment, and the value-carried source
boundary lineage specified by ordinary evaluation; do not capture a snapshot
of the live handler stack unless the source transition explicitly places that
lineage in the value. Let `θ` be the same injective, capture-avoiding map over
the code's free symbolic identities, the environment, typed-family formulas,
owned occurrences, and compile-time boundary binders. It fixes concrete
runtime event/activation IDs and the live store. If closure creation returns
that value without evaluating its body, and application evaluates the body
under the captured environment extended by the argument and the source-defined
lineage re-entry, then:

```text
Tr_θ(Closure(e,η,lineage)) = Closure(Tr_θ(e),Tr_θ(η),Tr_θ(lineage))
Tr_θ(ApplyValue(cl,v,c))
  = ApplyValue(Tr_θ(cl),Tr_θ(v),Tr_θ(c))
```

The first equation follows from structural transport of the code, environment,
and captured boundary evidence. For the second, both applications reduce to
the body `Run` relation with corresponding environments; apply its
equivariance and the state-threading bind equation above. Therefore every
finite request prefix of a later closure call is mapped together with its
typed endpoint, `K,D` incidence, source origin, and compile-time boundary
identity. A use-site freshening maps each binder once across the complete
closure interface. The lemma rules out reconstructing a callback effect only
after materializing the closure's concrete row.

This result is conditional on the source closure, environment-capture, and
re-entry rules being equivariant. It does not establish that an escaped request
is visible to a particular later handler, that its latent Function contract
contains all such requests, or that non-injective intrusion preserves complete
solution fibers. Those remain separate source-adequacy and principality gates.

**Pattern-binding transport.** Extend `Tr_θ` structurally to patterns and
their embedded expressions. Assume it fixes field/constructor labels,
preserves the runtime present/missing test, and that each atomic pattern test
and embedded-expression `Run_ν` judgment is equivariant under `θ`. Assume the
composite pattern rules are built from relational choice, composition, and
projection over child bindings. Then `BindPat` is equivariant by structural
induction. Its record-default case reduces to the following corollary. For a
field with subpattern `p` and default `e`:

```text
Tr_θ(BindField_{p,e}(r,η,s)) =
  BindField_{Tr_θ(p),Tr_θ(e)}(Tr_θ(r,η,s))
```

When the field is present, use the induction hypothesis for `p`. When it is
missing, apply `Run` equivariance and then the resumable-bind lemma above; the
resumed default continuation still reaches the transported remainder of the
pattern. Alias and alternation rules preserve equivariance by composition and
relational choice when their child rules do. A `RuleExpression` pattern must
use its embedded-expression evaluation relation and its equivariance theorem;
the syntax reference does not supply that semantic premise. Since `Tr_θ` maps
each request formula and incidence with the same identity action, it transports
typed-family constraints emitted by a
default through freshening or injective parent renaming without rebuilding
them from the residual row. The result is conditional on source `BindPat`
adequacy and injective transport; it does not prove source typing of field
presence or the non-injective parent quotient theorem.

#### Conditional handler naturality under solver substitution

Type solving can be non-injective on flexible type variables without merging
source request, family-owner, or handler identities. Let `σ` be a
homomorphic type substitution that fixes rigid imports and operation/family
constructors. Let `T_σ` substitute only type endpoints and typed request
arguments, with induced assignment `σ*ν'`; it acts as the identity on request
occurrences, family-ownership groups, and handler activation identities.
Assume type and argument denotations are substitution-natural, and that the
source handler transition bases arm matching and typed compatibility only on
those denotations plus the unchanged operation and visibility identities.
Write `H_κ(O)` for the semantic handler image of the observable interface
defined above. Then:

```text
T_σ(H_κ(O)) = H_κ(T_σ(O))
```

For `Return`, substitution preserves the value/arm typing premises. For a
request, exact operation and route tests are fixed; family and signature
predicates commute with `σ` by naturality; the forwarded or selected branch
therefore agrees on both sides. Arm output and raw/forwarded continuations
are substituted by the same homomorphism. Induction gives equality of finite
observations and their support projections. Because source occurrence and
owner identities are not substituted, this naturality permits distinct
family requests to become equal in type payload while their source groups
and evidence remain distinct.

This is the handler counterpart of filter transport through solving. It only
shows formula/transition naturality on assignments factoring through `σ`;
it does not show that every original solution factors through the solver
substitution, so it is not a solver completeness or principality theorem.

The pointwise law lifts to the complete relational image only with
two-directional coverage. Define the factor-assignment reindexing
`σ^*R = { (ν',T_σ(O)) | (σ*ν',O) ∈ R }`. Assume the concretization,
transition relation, and output observation are natural under the same map:

```text
C_ρ(T_σ(O),ν') = T_σ[C_ρ(O,σ*ν')]
Step_{H,κ,ρ}(ν',T_σ(O),T_σ(c),T_σ(c'))
  iff Step_{H,κ,ρ}(σ*ν',O,c,c')
Obs_H(T_σ(O),ν',T_σ(c'))
  = T_σ[Obs_H(O,σ*ν',c')]
```

The `Step` equation is equality of the transported and target transition
relations, not only agreement on pairs already written as
`T_σ(c),T_σ(c')`: every transition from a target configuration in the
transported concretization must have a source preimage. The `Obs_H` equation
likewise requires every target observation at such a successor to lie in the
image of a source observation. These backward-lifting clauses rule out extra
target successors or outputs that have no source witness.

Then the relational handler image satisfies:

```text
σ^*(H#_κ(R)) = H#_κ(σ^*R)
```

Each side is generated by corresponding reindexed witnesses `(O,c,c')`.
Concretization coverage supplies input witnesses, transition equality with
backward lifting supplies successor witnesses in both directions, and
observation equality with backward lifting supplies output witnesses in both
directions. This is exact on assignments factoring through `σ` and proves
that handler residualization can transport symbolic family constraints through
a solve step without reconstructing them from the output row. It still does
not show that all source solutions factor through `σ`, nor that the output has
a finite principal presentation.

### Shared-witness formula under symbolic transport

The interval-valued family constraint has a direct transport law in the
candidate denotation already recorded in the effect proof notes. For a
source-derived indexed batch `B`, let `g_B` be its owned shared-family
identity and define

```text
FamAgree_A(B,g_B,ν) iff
  ν(g_B) ∈ ⋂ { ArgDen_A(args(o),ν) | o ∈ B }
```

The existential projection `∃b. b ∈ ⋂ ArgDen_A(...)` says only that some
common inhabitant exists. It is adequate for testing nonemptiness, but it is
not a replacement for `FamAgree_A(B,g_B,ν)` in a scheme relation when `g_B`
also occurs in roots or other requests.

Assume the chosen argument denotation is natural under a type substitution
`θ`, including its complete tuple dependencies:

```text
ArgDen_A(θ(args(o)),ν') = ArgDen_A(args(o),θ*ν')
```

For an ownership renaming `h` with `ν'(h(g_B)) = (θ*ν')(g_B)`, substitution
preserves the whole assigned shared-witness formula:

```text
FamAgree_A(B[θ],h(g_B),ν') iff FamAgree_A(B,g_B,θ*ν')
```

Proof: apply the denotation identity to each indexed occurrence; the two
families of tuple sets are equal, hence so are their intersections and their
nonemptiness. This uses one intersection over the entire batch, so it
preserves cross-position and N-way dependence; it does not reduce the formula
to pairwise compatibility. A point-valued `InvArgs` encoding is a valid
replacement only when a separate theorem proves that it denotes this same
relation for the chosen arguments.

The whole joint request relation has the corresponding transport law. Let
`m` map request occurrences bijectively and `h` map source-owned shared-binder
identities bijectively, preserving the grouping relation
`g'(m(o)) = h(g(o))`. `h` is an ownership map, distinct from the type
substitution `θ`: two source instantiation groups remain distinct even if
solving makes their type arguments equal. Assume `θ` is natural for
`ArgDen_A` as above, with assignments related by pullback and
`ν'(h(g)) = (θ*ν')(g)` on shared-binder values. Then the ownership/occurrence
transport gives a bijection:

```text
Tr_{m,h}(J_R(θ*ν')) = J_{R[m,θ]}(ν')
```

The forward direction preserves every binder's common-intersection
condition by the denotation identity; the inverse uses `m⁻¹` and `h⁻¹`.
Request heads are fixed and every request argument is read from the
corresponding mapped assigned binder, so both directions preserve `Q`.
Therefore the `TypedRow` projection and its pointwise support inclusion
commute with this transport when both row operands use the same maps on shared
identities. This permits non-injective *type substitutions* during solving
when source ownership identities remain distinct and all formulas are
substituted together. It does not permit a non-injective map on the shared
binders, occurrences, or parent identities; those can change the joint fiber
and require the separate quotient criterion.

#### Solving as a solution-complete substitution

The pullback law separates formula transport from the completeness obligation
for a solver step. Let `σ` map old type variables to terms over residual
variables, and let `σ*ν'` be its induced source assignment. Homomorphic
substitution and `ArgDen_A` naturality give:

```text
Sat_{ν'}(K_C[σ], I[σ]) iff Sat_{σ*ν'}(K_C, I)
```

This is exact on assignments that factor through `σ`; it remains valid when
`σ` identifies type variables. A solve step preserves the complete solution
relation only if every source solution relevant to the exported observations
has an observationally equivalent factorization through `σ`. Under that
condition, the target relation loses no source observable, while the displayed
equivalence prevents it from inventing one. For a first-order equality
unifier, the usual most-general-unifier property supplies this factorization;
for polarized subtype solving, that property must be proved for the actual
solver and must not be inferred from equality unification.

Throughout this step, request occurrences, source shared-binder identities,
formula incidence, and boundary identities travel by their own identity maps
(identity maps when they are unchanged), not by `σ`. Thus unifying the type
payloads of two independent family uses does not silently merge their
ownership groups. The `FamAgree_A` and `J_R` relations remain symbolic
formulas in `K_C[σ]`; materialized rows do not regenerate them. This is a
conditional solver-preservation theorem, not a characterization of the
current solver's solve step.

Use one occurrence/owner map alongside `θ` for the formula's incidence. For
solving, apply the solution substitution to both endpoints and occurrence
payloads and keep the resulting formula attached to every dependent view.
For residualization, the request row may change but the formula remains in
the coupled relation until its dependency is discharged by proof. For
generalization, bind the locally owned endpoints and formula together while
fixing outer identities. For a use-site instantiation, rename all batch
occurrences, endpoints, and incidence with the same injective map. For
intrusion, apply the parent map to endpoints and evidence payloads, and the
boundary map to route lineage. Substitution and injective renaming use the
displayed reindexing law; residualization and generalization additionally
need their own incidence and fiber-preservation laws.

With a non-injective parent map, the displayed pullback identity still holds
syntactically, but it does not prove that two formerly independent source
assignments or root observations can be merged. That requires the separate
quotient/fiber theorem. Likewise, naturality of `ArgDen_A` for intervals,
compound types, and shared tuple positions has not yet been proved, and this
lemma does not establish which source rules create `B`. Its result is narrower
but concrete: once a source rule has created the symbolic batch, substitution
can transport that very batch without rebuilding it from materialized rows.

For the simple bounded-type fragment, naturality reduces to an ordinary
structural lemma. Assume type interpretation is compositional and satisfies
`⟦θτ⟧_{ν'} = ⟦τ⟧_{θ*ν'}`. Define an interval argument denotation by
`ArgDen_A([L,U],ν) = { a | ⟦L⟧_ν ≤ a ∧ a ≤ ⟦U⟧_ν }`, with the subtype
preorder fixed independently of the solver representation. Then:

```text
ArgDen_A(θ([L,U]),ν') = ArgDen_A([L,U],θ*ν')
```

Both sides are the set of `a` satisfying the same two inequalities after
rewriting each endpoint by the interpretation identity. For a tuple of
arguments, interpret the entire tuple under the one assignment before
forming `ArgDen_A`; do not replace it with a product of independently
projected positions unless that factorization is proved. The shared-witness
formula then follows by the same intersection argument above for any finite
batch. This closes substitution naturality conditionally for this interval
fragment. It does not define the full Yulang denotation for unions,
intersections, nominal recursion, or Function/effect arguments, nor show that
the source generates the intended batches.

The shallow operational cases are consequences of the same image. A covered
visible request enters its arm with the raw continuation; a request not
selected at this activation is forwarded with the shallow wrapper around its
continuation; any request emitted by an arm is observed in that arm's output
computation. A one-shot family removal is valid only if the image proves the
family absent from every output observation represented by that fiber. When
the carrier cannot express that fact, it must keep the family or use a sound
coarser image. Thus `Drop` certificates, route ledgers, and `Demand` edges can
serve as proof or implementation evidence for computing this image, but none
is an independent semantic rule.

A direct shallow trace refutes subtraction based only on matching the first
request. Let `q` be one well-typed request instance, with continuation
`k(r)=Request(q',c',k')` where `q'` has the same row key as `q` (same
operation and family arguments) and the arm signature accepts both
payload/result instances. Let the `q` arm resume its raw continuation once and
return its result. The first `q` is consumed at this activation, but `q'` runs
outside the activation and appears in the handled output trace. Thus the row
key of `q` belongs to both input and output support, while the row difference
`supp(c) \ {q}` is empty. This counterexample uses one
resume; two sequential occurrences suffice, and it does not depend on Oracle
weights, repeated continuation use, or typed-family ambiguity. It follows
directly from the shallow raw-continuation clause; only the complete handler
image can justify a family-wide `Drop`.

This removes source-site-specific subtraction from the mathematical core,
but the transfer remains deliberately abstract. A family may occur in an
input path and not in the output path after non-resumption; another may escape
only through a resumed raw continuation; an incomplete or invisible request
is forwarded. The transformer distinguishes these by executing the same
shallow relation on continuation-bearing computations, not by applying one
row-level subtraction formula. For may-rows, the computable result must
over-approximate the support of `H#`; it must not assume that `H#` distributes
over row union.

The unresolved work is to define a finite symbolic representation whose
denotation is this dependent relation and whose output projection is both
computable and principal. In particular, symbolic typed-family invariance,
owner incidence, and route lineage must survive in the formula presented to
the solver. Grounding each fiber and rebuilding those constraints from
materialized rows would not implement this definition.

### The collecting support projection and two kinds of union

For one fixed admissible valuation `ν`, let `γ(A,ν)` be the concrete
continuation-bearing computations represented by an abstract input interface
`A`. Define the handler's may-support reference transfer by:

```text
May_H(A, ν) = ⋃ { TraceSupport(H_κ(c)) | c ∈ γ(A, ν) }
```

`TraceSupport` is a set of typed request instances appearing on finite traces
of the handled computation, including arm requests and requests exposed by
shallow resumption. The definition is indexed by `ν`, rather than merging
ground instances from different valuations. The symbolic input relation
continues to state which valuations and occurrence groups are admissible.

For this fixed fiber, the support theorem is direct: every result represented
by `γ(A,ν)` has each of its finite-trace requests in `May_H(A,ν)`. It is also
least in the full powerset of typed request instances: if a set `E` bounds
every result of `H_κ` on `γ(A,ν)`, then every element of the union defining
`May_H(A,ν)` belongs to `E`. This exact collecting projection is a semantic
reference, not a requirement that the compiler track exact traces or
continuation usage. A practical finite row language may over-approximate this
set; its principality claim must then be relative to its own expressible
ordering and denotation.

#### One abstraction-congruence test for relational operations

There is a general criterion for deciding whether a finite interface can
carry a relation exactly without re-expanding its concrete fibers. Let
`T ⊆ X × Y` be a source relation and define
`T(x) = { y | (x,y) ∈ T }`. Let `α_in : X → A` and `α_out : Y → B` be the
chosen input and output presentations. An exact abstract transformer `t`
satisfying

```text
t(α_in(x)) = { α_out(y) | y ∈ T(x) }
```

exists on the image of `α_in` exactly when

```text
α_in(x) = α_in(x')  ⇒
  { α_out(y) | y ∈ T(x) } = { α_out(y') | y' ∈ T(x') }
```

for every `x,x' ∈ X`. Equality includes the empty set, so the presentation
preserves whether a complete abstract output is represented; it does not by
itself distinguish divergence from stuckness. Such outcomes must be included
in `Y` if the chosen observation distinguishes them. Necessity follows by
applying `t` to the equal abstract inputs. For sufficiency, define `t(a)` by
the output set of any representative `x` with `α_in(x)=a`; the premise makes
that definition independent of the representative. For deterministic total
operations this reduces to equality of the two abstract outputs.

For a local bind, typed boundary, or handler step, `X` and `Y` may be fixed
`(ρ,ν,κ)` fibers. Generalization and intrusion instead act on complete
assignment-indexed relations: their `X` and `Y` must include every admissible
assignment, rigid import, owned identity, root observation, and the relevant
projection or parent transport. Checking congruence at one `ν` does not prove
preservation of those whole-relation fibers. This is a criterion on a
presentation, not a new source rule. It applies uniformly to existing source
relations and lifecycle maps, exposing where a proposed abstraction forgets
information that a later composition observes.

A support-only input fails this exactness test for shallow handler transfer.
At one fixed assignment, take two computations with the same operation,
payload, family instance, and typed may-row `{F}`:

```text
c₀ = Request(F, (), λ_. Return(v))
c₁ = Request(F, (), λ_. Request(F, (), λ_. Return(v)))
```

Let the visible `F` arm resume the raw continuation once and return its result.
The first `F` is consumed in both computations. Shallow handling runs the raw
continuation outside that activation, so the outputs have request supports
`∅` for `c₀` and `{F}` for `c₁`. The input support abstraction identifies
`c₀` and `c₁`, but their exact output support observations differ. Therefore
no pointwise exact handler transformer can factor through that input row
alone, even when typed-family and payload facts are identical. This is a
continuation correlation, not a reason to add another row selector.

For this counterexample, instantiate `T` with the typed shallow-handler
relation at one fixed `(ρ,ν,κ)`, and let `α_in` observe only the typed may-row.
The failure does **not** make the collecting `May_H` undefined and does not
require exact continuation-sensitive inference. For the two exhibited
computations together, the collecting output support is their union `{F}`, a
sound row result. A finite solver may use the collecting support for a whole
abstract fiber if it is least in its declared output ordering and if later
operations remain sound and principal under the same abstraction.
More generally, a candidate output abstraction needs a least representable
upper bound of `{ α_out(y) | x∈γ(a), y∈T(x) }`; a finite syntax does not by
itself guarantee that such a bound exists. When the output carries symbolic
typed-family predicates, the bound must retain their same-assignment
incidence `K,D` rather than unioning only materialized supports. The same
test can be applied to callback composition, filtering, generalization, and
intrusion, using their appropriate whole-relation input/output maps.

Two unions must not be conflated. Relational disjunction `R ∪ S` chooses one
of two complete interface relations. Pointwise row join `A ⊔row B` combines
support coordinates inside an interface and admits computations that mix
requests from both rows. The first obeys exact relational-image distribution
for a fixed `H_κ`, because its concretization is a union. For row join,
`γ(A,ν) ∪ γ(B,ν) ⊆ γ(A ⊔row B,ν)`, so monotonicity gives only:

```text
May_H(A,ν) ∪ May_H(B,ν) ⊆ May_H(A ⊔row B,ν)
```

Equality requires an additional theorem about the row concretization and
handler behavior. A finite row abstraction that forgets correlations may make
the inclusion strict. This distinction is why relational composition can be
the common core while splitting a may-row cannot by itself justify applying a
handler transfer separately to each half.

The strictness can arise from losing a value/effect correlation. Let a
previous transformer `H` have two possible outputs: `Request(A,(),λ_.Return(0))`
and `Return(1)`. Their collected support is `{A}`. A support-only
concretization of `{A}` also admits `Request(A,(),λ_.Return(1))`, which was not
an output of `H`. Let `G` handle `A` by resuming its raw continuation and emit
`B` only when the resumed result is `1`. Then `G` after either actual output of
`H` emits no `B`, but `May_G({A})` contains `B` because of the extra admitted
computation. Thus abstraction between the two transformers makes
`May_{G∘H}(X) ⊊ May_G(May_H(X))` for the two-output input fiber `X`. A complete
relational interface can avoid this particular widening only if it retains
the value/effect correlation; a may-row cannot assume exact handler
composition.

In the corresponding complete interface relation, keep the alternatives
separate:

```text
Rel_H(X) = { (value=0, row={A}), (value=1, row=∅) }
Rel_G∘Rel_H(X) = { (value=0, row=∅), (value=1, row=∅) }
```

The first `G` result comes from resuming `A` and observing `0`; the second is
the pure value arm. No branch emits `B`. The widened support concretization
adds `(value=1,row={A})`, and only that invented pair reaches `G`'s `B` arm.
Thus ordinary relational composition preserves this example exactly, while
projecting to a may-row and concretizing again does not. This is an
extensional proof-reuse advantage for the coupled-relation candidate, not yet
a finite-solver or source-adequacy result.

For the direct shallow fragment, the trace rules give the corresponding
operational cases: `Return` executes the value arm; a covered, eligible
request executes its operation arm with the raw continuation; an uncovered or
ineligible request is forwarded with the handler around its continuation.
Applying the support projection to those outputs includes arm effects, keeps
forwarded requests, and includes any suffix exposed by raw resumption. This
checks the image definition against the direct trace model without introducing
a separate subtraction rule. The callback/thunk visibility extension and its
finite symbolic presentation remain open, so this is not yet the complete
source-to-inference proof.

The callback `call` / `invoke` witness is an instance of ordinary invocation
composition. Its pure argument permits a small sequencing lemma, but that
lemma is evidence for the general relation, not a callback-specific source
rule. Effectful or deferred argument behavior must come from the source
computation semantics. No runtime `pure_mono` test is promoted into the
mathematical core.

## One lifecycle relation, distinct preservation laws

All lifecycle operations act on the complete coupled relation, including
typed-family formulas and their incidence:

```text
solve            substitute symbolic endpoints, preserving the relation
residualize      relational image through the source handler/effect context
generalize       retain the fixed-ρ fiber while quantifying owned identities
instantiate      capture-avoiding renaming of one use's owned identities
intrude          transport through parent map P and boundary map Θ
```

The proof obligations differ even though the carrier is shared. Solving needs
solution-fiber preservation. Residualization needs sound relational image and
least representable projection. Generalization needs exact fixed-`ρ` fiber
projection and the independent-use product law. Fresh instantiation needs
equivariance under one consistent renaming of every occurrence and formula.
Injective intrusion may use the same kind of equivariance; non-injective
intrusion needs a quotient theorem preserving every observable root and
request/handler view. No single renaming slogan proves all these cases.

`P` and `Θ` may remain separate implementation maps because they act on
different identities. Mathematically they are components of one transport
action on `Rel_C`; symbolic family endpoints and evidence payloads receive
`P`, while boundary lineage receives `Θ`. A type substitution never erases
boundary evidence merely because request support becomes equal.

The pure Simple-sub audit supplies a stress case for `P`: ordinary extrusion
memoizes representatives by `(variable, polarity)`, and its two representatives
can admit independent boundary choices. For a variable with lower bound
`Int` and no informative upper bound, the positive representative may be
`Top` while the negative representative is `Bottom`; identifying both loses
that assignment pair. This is recorded as evidence against claiming that
one parent per variable is ordinary Simple-sub extrusion equivalence, not as
a requirement to add polarity-indexed semantic selectors. The unified
relation must either retain both directional constraints in its complete
formula and prove the exported root observations are preserved, or show by
the quotient criterion below that the source relation itself entails the
identification. Separate polarity ports, if used in a finite presentation,
are then solver coordinates whose meaning follows from those constraints.
See `notes/progress/2026-09-30-simple-sub-paper-mlsub-audit.md` for the
reference discriminator and its scope.

### Generalization and fresh use as abstraction and reindexing

This gives an exact lifecycle lemma without a special rule for typed-family
obligations. Fix one complete generalizable view `V`: this is a member-root
view selected at its source generalization boundary, or a tuple if one source
use event exposes several roots jointly. Let `K_V(ρ,ω,I)` present that view,
and let `Ω_V` contain its owned semantic binders: type and row variables,
plus any other identities whose assigned values occur in the interface
relation. `ρ` is the fixed outer environment of that view. If root preparation
produces several versioned views, keep their relations distinct until a
simulation proves they are projections of one relation; do not infer one
component-wide binder set from SCC membership alone.

`K_V` includes every source-derived family-invariance formula. The finite
presentation `I` also records source-binder sharing, request occurrences,
owner incidence, and locally bound handler identities. Those labels are not
extra assignment coordinates: `I` is considered modulo consistent relabeling
that preserves the sharing and boundary structure. Generalization packages
`(Ω_V,K_V,I)` as a scheme template, binding the owned semantic identities and
leaving `ρ` free. It does not evaluate `K_V` after materializing rows or drop
its incidence structure.

The identity action is sort-preserving but shared across all occurrences of
one identity. In particular, when a source `TypeVar` occurs in a value type,
recursive bound, and Function latent-effect position, every occurrence maps
through the same `ι`; these positions do not get independent fresh copies. If
a successor representation has a genuinely distinct row-tail binder sort,
its binders also receive one consistent injective map, without splitting any
source identity that the typing relation shares across type and effect views.

For one use, choose a capture-avoiding bijection `ι` from `Ω_V` onto fresh owned
identities, fixing `ρ`. Extend it to an isomorphism `î` of the presentation's
occurrence, owner, and handler labels. This isomorphism must preserve request
heads and payload/result positions, formula endpoints and incidence, the
partition into shared-binder groups, owner-to-view incidence, and handler
activation links and stack order. Rigid imported identities and source
constructors are fixed. Instantiate by reindexing the *whole* presentation:

```text
K_{V,ι}(ρ,ω',I') = K_V(ρ, ι⁻¹(ω'), î⁻¹(I'))
```

where `î` consistently relabels presentation indices and leaves fixed outer
identities and source constructors unchanged. For each source assignment `a`
and target assignment `a'` related by `a'(ι(x)) = a(x)` for all semantic
binders `x ∈ Ω_V` and equal on `ρ`, structural satisfaction gives:

```text
a' ⊨ K_{V,ι}(ρ,ω',I')  iff  a ⊨ K_V(ρ,ω,I)
```

The proof is induction on the formula and interface syntax. Atomic type and
row relations are unchanged under the corresponding reindexing; a
`FamAgree_A` atom has the same source-binder sharing groups and argument
denotations; and conjunction/disjunction preserve equivalence componentwise.
Therefore every independent use gets an isomorphic satisfying fiber when it
receives a disjoint `ι`, while all uses retain the same rigid outer
assignment. No formula is regenerated from its materialized row. For an
SCC's internal use, there is no `ι`: its roots and formulas remain in the
live component relation.

This is exact for injective alpha-renaming and establishes the typed-family
lifecycle requirement across generalization and fresh instantiation at the
relational-presentation level. It does not prove that source lowering builds
the correct `K_V` and `I`, that a solver preserves them, that an implementation
stores every required incidence edge, or that non-injective solving/intrusion
preserves fibers. Those remain separate correspondence and quotient
theorems; identity reindexing cannot justify merging independent variables.

#### Joint uses under a shared receiver context

For a finite set of independent source instantiation events `U`, give each
event `u` a copy map `(ι_u, î_u)` of the kind above. Require pairwise disjoint
owned ranges, all disjoint from the shared receiver identities `ρ`; each map
fixes `ρ`. The product map acts by the corresponding copy map on each local
namespace and by identity on `ρ`. Let `W` be any well-sorted joint receiver
constraint/observation formula over `ρ` and the use-local views. It may
correlate distinct uses; it need not factor into per-use conjuncts. If it is
transported by the product map, then a joint assignment satisfies

```text
(⋀_{u∈U} K_u) ∧ W
```

iff its transported assignment satisfies

```text
(⋀_{u∈U} K_u^{copy}) ∧ W^{copy}
```

Proof: the product map is a bijection on the disjoint local assignment
domains and identity on the receiver domain. The single-use structural
satisfaction equivalence applies to each `K_u`; equivariance of `W`
preserves any cross-use relation. Thus the complete joint satisfying fiber is
preserved without asserting that it factors. A `TypeVar` shared across value,
recursive, and Function-effect positions uses the same `ι_u` in all three.
This is only a renaming theorem for source events already known to be
independent; it neither establishes the source's event partition nor proves
the independent-use product equation or SCC-root scheduler simulation. This
is the coupled-interface form of the reviewed conditional joint-use theorem
in `notes/progress/2026-09-30-intrusion-joint-use-renaming-review.md`.

### Exact criterion for a non-injective parent quotient

Let `P` fix outer identities and map intruded owned identities to parent
identities, possibly identifying several owned identities. Let `Ω_C` be the
source-owned identities and `Ω_P = range(P)` include parent identities and
any component-local identities that `P` leaves fixed. A target assignment `μ`
assigns every identity in `Ω_P`; its pullback `P*μ` on `Ω_C` is defined by
`(P*μ)(x)=μ(P(x))`. Define the quotient by evaluating the original formula
under that pullback and transporting the complete interface. First fix one
source presentation template `I`:

```text
K_P(ρ,μ,I[P]) = K_C(ρ, P*μ, I)
```

If the source relation ranges over multiple interface presentations, its
quotient is their direct image, not a choice of one preimage formula:

```text
Rel_P(ρ) = { (μ,I') | ∃ν,I.
  ν = P*μ ∧ I' = I[P] ∧ K_C(ρ,ν,I) }
```

Thus different source presentations that map to the same `I'` contribute by
relational union. The fixed-template formula above is the corresponding
fiberwise instance of this direct image.

Every satisfying quotient assignment `μ` lifts to the source assignment
`P*μ`, so this construction cannot add source solutions. It can remove
solutions: it keeps only assignments that are constant on every fiber of
`P`. Let `Obs_C(ρ,ν,I)` be the complete external observation chosen for
principality, including every projected root and the typed request/handler
behavior clients may constrain. The quotient preserves the source relation
exactly up to that observation iff:

```text
for every (ν,I) satisfying K_C(ρ), there exists μ such that
  K_P(ρ,μ,I[P]) and
  Obs_C(ρ,ν,I) ≈_Obs Obs_P(ρ,μ,I[P]).
```

Here `Obs_P` evaluates the transported interface under the target assignment.
The criterion also assumes the naturality equation
`Obs_P(ρ,μ,I[P]) ≈_Obs Obs_C(ρ,P*μ,I)` whenever the source and target
presentations are related by `P`.

The forward direction is exactly the condition that every source observable
has a `P`-constant representative; the reverse direction follows from the
lifting property above. This is necessary and sufficient for the direct
quotient construction, but not by itself a practical solver test: both the
source relation and the complete future-client observation must be defined.
The point-fragment entailment condition below is a tractable sufficient
criterion for one chosen `≈_Obs`; `FamAgree_A` alone fails the exact criterion
for the interval counterexample that follows.

**Origin-sensitive observation test for a parent quotient.** Instantiate
`Obs_C` with the complete request/handler observation: request origin, typed
payload and `K,D` incidence, ordered visibility/selection, and the resumable
suffix. Two same-family, same-payload requests can still differ because one
origin has `Capture(o_cb,h)` and the other caller origin lacks it. If ordered
search handles the former and forwards the latter, a quotient that also
collapses their owner labels and replaces the edge evidence with one
node-local capture value cannot factor this observation: granting capture to
the merged label hijacks the caller request, while denying it loses the
callback request's eligible route. This is an adversarial test of the
observation-factorization premise, not a claim that a type-only parent map is
invalid. A type-only quotient may retain injective owner and boundary maps and
keep both request edges distinct; it must still satisfy the complete
solution-fiber criterion above, including `K,D` and use-site observations.

### A sufficient parent-quotient condition (point fragment)

There is a useful sufficient condition for non-injective intrusion that is
stronger than the substitution pullback identity. Let `P` map the component's
exported type-variable identities onto parent identities and fix
component-local identities that are not intruded. Let `K_C(ρ,ν,I)` be the
exact finite point-fragment relation, and let `μ` assign every identity in
`range(P)` (parents and retained locals) while `ρ` stays fixed. Write
`(P*μ)(x)=μ(P(x))` for the induced source assignment. Define the quotient by
direct substitution:

```text
K_P(ρ,μ,I[P]) = K_C(ρ, P*μ, I)
```

Assume:

1. `P` fixes all rigid outer identities and leaves occurrence, owner, and
   boundary identities distinct; it identifies only type-variable
   identities.
2. For every pair `x,y` in the same fiber of `P` that occurs in `K_C` or a
   jointly observable root/request view, `K_C` entails `ν(x) ≈ ν(y)` for every
   satisfying assignment, where `≈` is the selected point-type equivalence.
3. Type constructors in `I` and formulas in `K_C` respect `≈`, so replacing
   one equivalent point endpoint by the other preserves their denotation.

Then quotienting these identities preserves the complete interface solution
fiber up to `≈`. In one direction, for each source solution choose one
representative value for each fiber of `P`. Premise 2 says every source value
in that fiber is equivalent to the representative, and premise 3 makes
replacing them by that representative preserve `K_C` and the root views.
Thus every source solution factors through `P` modulo `≈`. In the other
direction, every quotient solution lifts by assigning each source identity
the value of its parent (retained locals keep their own assigned value), and
the definition of `K_P` makes that lift a source solution. The observable
interfaces agree modulo `≈` by premise 3 and observation naturality. Thus this
quotient loses no satisfying interface and introduces none in this fragment.

This proof transports the whole formula; it does not delete `FamAgree_A` or
reconstruct it from rows. If two merged identities were independent under
`K_C`, the second direction would still lift, but the first would fail for
source solutions assigning them different types. The familiar roots
`F<α>` and `F<β>` demonstrate that failure. For interval-valued identities,
common-witness compatibility is weaker than point equivalence, so premise 2
cannot be replaced by `FamAgree_A`. Non-injective intrusion outside these
premises still needs the general quotient/root-observation theorem; injective
transport remains the renaming case.

Concretely, take the point-interface fragment `K_C = True` with two exported
closure roots whose latent rows are `F<α>` and `F<β>`. The complete observation
is the ordered pair of root rows. The satisfying assignment
`α=Int, β=Bool` distinguishes those roots. A parent map that identifies
`α,β` can produce only pairs `(F<t>,F<t>)`, so no parent assignment represents
that source observation. This is a direct counterexample to unconditional
one-parent-per-SCC-variable sharing. It is an interface-level discriminator;
whether a particular source SCC can generate exactly this pair is a separate
source-adequacy question, not needed to reject the unconditional quotient
claim.

There is a source-level witness for this discriminator using a mutually
recursive definition SCC and parameterized effect types:

```yulang
act pulse 'a:
  our fire: 'a -> 'a

my spin() = spin()
my f(x: () -> [pulse 'a] 'a, y: () -> [pulse 'b] 'b) = case false:
  true -> case g(\() -> spin(), \() -> spin()):
    _ -> ()
  _ -> ()
my g(u: () -> [pulse 'c] 'c, v: () -> [pulse 'd] 'd) = case false:
  true -> case f(\() -> spin(), \() -> spin()):
    _ -> ()
  _ -> ()

my int_cb() = pulse::fire 1
my bool_cb() = pulse::fire true
my use_f = f(int_cb, bool_cb)
my use_g = g(bool_cb, int_cb)
```

The `true` branches create mutual source references; the executed `false`
branches return unit. The bottoming `spin` callbacks allow the recursive calls
to typecheck without relating the member parameters. From a clean frozen
`a58eefc3` build, `check` succeeds, `run --interpreter` succeeds, and the raw
scheme dump shows distinct quantified type identities for `f`'s two callback
parameters (`'23`, `'28`) and for `g`'s (`'53`, `'66`). Each endpoint remains
inside its own `pulse` family-argument row. The concrete uses instantiate
`f`'s pair as `pulse<int>` and `pulse<bool>`, and `g`'s pair in the reverse
order; both are accepted and execute. Thus one member root in this source SCC
jointly observes two independent typed-family endpoints at a single incoming
use. Identifying them with one parent cannot represent `use_f` or `use_g`;
this is a source-level counterexample to an unconditional non-injective merge,
not merely an abstract interface witness. The exact commands and captured
quantifier evidence are recorded in the current progress entry.

The distinction has a concrete interval witness. In the finite chain
`Never < Int < Any`, let independently observable roots `x` and `y` have
admissible values `[Never,Int]` and `[Int,Any]`. Their family-argument
denotations have the common witness `Int`, so the shared-witness relation
holds. The source relation still admits the joint root assignment
`x=Never, y=Any`. A quotient identifying `x` and `y` admits only the
intersection `[Never,Int] ∩ [Int,Any] = {Int}` and loses that source solution.
Thus a shared inhabitant proves compatibility of the two sets, not equivalence
of the symbolic identities. The quotient condition must inspect the complete
joint interface solution relation, not just the family-coherence projection.

## Principality and finite presentation

The relation above is intentionally more expressive than any proposed solver:
an unrestricted set of satisfying interfaces may not have a finite
presentation or terminating principal projection. The successor must select
an expressible fragment and define subsumption on its complete interfaces.
For fixed imports `ρ`, a principal result must denote the most-general
representable interface satisfying the source constraints, and separate
incoming uses must denote independently renamed copies over the same rigid
`ρ`. This criterion is relative to the chosen abstraction, not to exact trace
support and not to Oracle's intermediate scheme formatting.

Three candidate presentations remain to compare:

1. finite typed may-rows with symbolic family constraints;
2. constrained interface formulas whose denotation is `Rel_C(ρ)`;
3. a finite abstraction of continuation-bearing computation relations.

Compare them for soundness, representability, termination, principality,
composition, and proof reuse. Prefer the smallest one that satisfies the
proofs. A selector, obligation kind, or source-specific rule is justified only
if a source-level distinction cannot be expressed as a relation or projection
of this carrier. If Oracle routing conflicts with these proofs, record the
concrete counterexample, the dropped Oracle behavior, the adopted rule, and
the final-acceptance impact.

#### Candidate comparison and preferred layering

These are not three equally fundamental semantic choices. Candidate 3 is the
cleanest reference semantics: source evaluation denotes a relation over
continuation-bearing computations, and handlers are ordinary relational
transformations. It is compositional and reuses one handler proof, but exact
behaviors are generally too rich to serve as a finite principal inference
language. It is therefore a soundness reference, not the preferred compiler
representation.

Candidate 1 is the smallest likely executable abstraction. It can be finite
and familiar, but rows erase correlations; the handler image need not commute
with row join, and open duplicate rows already give a principality barrier for
eager matching. Symbolic typed-family formulas repair some lost information,
but a row-plus-ledger design risks promoting each solver bookkeeping category
into another semantic rule. Use this candidate only if its relation to the
source behavior and its principal projection are proved for the claimed
fragment.

Candidate 2 is the preferred bridge: present a source-derived solution
relation by a finite constrained formula, and define row views as projections
of that formula. Relational composition gives one account of callback
invocation, row restriction, handler transfer, and lifecycle substitution;
principality is stated in the chosen formula language. This has the best proof
reuse and compositionality if that language has terminating, principal
projection. That closure property is not proved, so this is a preference for
the next proof target, not a selected representation or implementation gate.

The comparison is conditional: none of the candidates is yet proved sound and
principal for the source language. Their current tradeoffs are:

| Candidate | Conceptual economy | Compositionality and proof reuse | Principality risk |
| --- | --- | --- | --- |
| Typed may-rows plus symbolic family formulas | Smallest likely solver language, but risks treating row matches and family ledgers as separate semantic mechanisms | Cheap support operations; handler/callback composition needs additional correlation lemmas | Eager match selection loses alternatives; open duplicate rows expose this directly |
| Constrained complete-interface relation | One semantic account for typed constraints, callback composition, handler images, and lifecycle transport; row selectors and route records become derived views/evidence | Strong reuse of relational image, restriction, reindexing, and fixed-outer projection laws | The relation may lack a finite terminating principal presentation; this is the main open theorem |
| Continuation-bearing source computation relation | Most direct account of observable execution and handler behavior | Source sequencing, callbacks, and handlers compose naturally | Usually too precise or large to be the inference language; abstraction may lose symbolic fibers |

The current proof strategy therefore uses the continuation-bearing relation as
the adequacy reference and tests the constrained complete-interface relation
as the inference-facing core. The typed-row candidate is a possible finite
presentation of that core, not a parallel semantics. This layering is
preferred only if a finite presentation can preserve the same fixed-outer
solution fibers and independent-use behavior. If it cannot, the correct
response is to narrow the supported expressible fragment or accept
conservative loss of precision, not to add one selector or obligation for
each Oracle source site.

Under this layering, a source distinction is fundamental only when it changes
the source computation relation, a complete typed interface, or which
assignments satisfy that interface. A filter name, `Sel_s` case, `Demand`
record, route certificate, or typed-family obligation is not independently
fundamental merely because the frozen implementation stores it separately.
Such objects may remain as finite proof witnesses when they are projections
of the common relation and their transport preserves its denotation. Handler
visibility remains a real semantic fact, but its bookkeeping representation
must be derived from the active source boundary and continuation behavior.

Keep mathematical facts distinct from their solver witnesses. A source
relation may depend on which requests are dynamically visible at a handler
activation, but a route ledger is only one way to prove that fact. Formula
incidence `D`, stable obligation keys, owner/version maps, and parent maps are
transport bookkeeping; they are not additional semantic coordinates unless a
source observation can distinguish them. Typed-family invariance belongs in
the denotation of the symbolic constraint formula, not in an independently
evolving obligation store. A transport implementation must preserve that
formula's satisfying fibers and all dependent projections; preserving its
bookkeeping graph alone is insufficient.

This gives a compact test for proposed special machinery: state the source
observation it distinguishes, then derive it from the complete relation. If
the machinery only tells the solver where to find or transport a formula, keep
it in the presentation. If no relation/projection can express a distinction
that changes source behavior or admissible solutions, do not add a semantic
construct for it.

#### Minimal relational algebra for the compiler-facing theory

The preferred formulation needs only a small operator basis over the one
complete interface relation. Fix imported identities `ρ` throughout each
operator. Let `R ⊆ A × I` relate assignments `ν ∈ A` to complete interfaces
`I`. For two independently described views `R₁ ⊆ A × I₁` and
`R₂ ⊆ A × I₂`, their fiber product is
`{(ν,i₁,i₂) | (ν,i₁)∈R₁ ∧ (ν,i₂)∈R₂}`. Let
`T ⊆ A × I × J` be a source-typed transition relation; source steps keep the
same assignment `ν`. The core needs four ordinary relational constructions:

```text
fiber product:   R₁ ×_A R₂ (join only equal assignments ν)
composition:     T ∘ R     = { (ν,j) | ∃i. (ν,i)∈R ∧ T(ν,i,j) }
restriction:     R ↾ P     = { (ν,i)∈R | P(ν,i) }
transport:       f_*R      = direct image under a consistent assignment/interface map
                 f^*R      = pullback along a map of assignments/interfaces
```

Projection is a direct image under the coordinate-forgetting map, so it does
not require a separate semantic primitive. It is among these interface maps,
not necessarily an identity renaming of type variables. A request-support
projection, for example, maps a complete interface to its row view while
leaving `ν` fixed.
Sequential source steps use composition at their shared complete interface:

```text
(U ∘ T)(ν,i,k) iff ∃j. T(ν,i,j) ∧ U(ν,j,k)
```

Its associativity follows by reassociating the two existential intermediate
interfaces; no source-specific law is needed for that step. A view projection
does not existentially discard a type assignment: it retains `ν` and every
constraint on it. Generalization is the separate abstraction boundary that
binds the component-owned identities.

The `ν` component is held fixed by source transitions. A transition may add
ordinary typing predicates to the same joined relation; it cannot solve a
typed-family formula by forgetting the assignment and rebuilding a row later.
`K` and its view incidence are a finite notation for that relation, not a
second operator or evolving obligation store. Image notation `T[R]` means
relational composition `T ∘ R`.

With those operators, the intended derivations are:

| Operation in the inference problem | Relational derivation |
| --- | --- |
| Source sequencing and callback invocation | Join on the shared value/environment interface, then compose with the source transition relation |
| Row splitting | Project request views while retaining the common assignment and every formula dependency that still constrains a surviving view |
| Filtering | Apply the source predicate to the request coordinate and map that coordinate to its filtered view, retaining the same assignment and all dependent predicates |
| Handler residualization | Compose with the declarative shallow-handler transition, then project its residual request support |
| Generalization | Abstract/close component-owned identities while retaining the relation over rigid imports and every exported root |
| Fresh instantiation | Rename all locally owned identities with one capture-avoiding injection, fixing the same rigid imports |
| Intrusion | Pull back the complete relation along the parent assignment map `μ ↦ μ∘P`; a non-injective parent map is valid only when the relation factors through its fibers up to the chosen observation equivalence |

This classification intentionally does not give rows, callbacks, handlers, or
SCC transport separate semantic rule families. Their source syntax supplies
different transition relations and interface maps; the proof obligations are
instances of relational composition, fiber product, restriction, and
consistent interface-map transport. Projection is a direct image under a
coordinate map; binder renaming changes type-identity indices.
Numeric selector IDs, demand edges, route certificates, and parent tables may
implement those operations, but they do not enlarge the semantic algebra.

Several tempting equations are not laws of this algebra. Projection need not
commute with relational image; handler image need not distribute over a union
of marginal rows; and a non-injective reindexing need not preserve the
solution fiber. Each such commuting or quotient step requires a preservation
premise for the complete relation. By contrast, relational composition is
associative, restrictions by `P` and `Q` compose as restriction by `P∧Q`, and
capture-avoiding injective renamings compose. These generic laws are the
proof-reuse target: source-specific results should follow from them plus the
source transition definition, rather than introduce new semantic selectors.

The table is a proposed factorization of the already stated carrier, not a
claim that all source typing rules have been derived. In particular,
source-owned invariant argument groups, activation-specific visibility, and
the exact binder scope of generalization must be supplied by source typing.
If one of those turns out to be a real distinction, represent it in the
relation or transition domain and prove its transport; do not encode an
Oracle storage detail as a new semantic constructor.

### Finite point-row constrained presentation (conditional lemma)

There is a finite presentation candidate for the point-valued closed-row
fragment that avoids choosing an eager row match. For finite rows `R` and
`S`, define symbolic inclusion by:

```text
RowIncl_A(R,S,ν) =
  GroupEq(R,ν) ∧ GroupEq(S,ν) ∧
  ⋀_{x ∈ R} ⋁_{y ∈ S, head(y)=head(x)} FamCompat_A(x,y,ν)
```

An empty disjunction is false. `GroupEq` requires each source-owned occurrence
group to denote one common argument tuple at `ν`; it is the nonempty-row
condition from the point-valued `RowSub` expansion above. For point-valued
family arguments, `FamCompat_A` is the symmetric subtype-equivalence formula,
under the conditional premise that this equivalence is the source argument
relation. Every occurrence in the formula shares the same valuation `ν`; no
disjunct is selected while another branch remains possible. A finite row
produces a finite formula DAG, and repeated subformulas may be shared without
changing its denotation. If group well-formedness is already conjoined in an
ambient `K_C`, the displayed `GroupEq` conjuncts are supplied by that shared
formula; they are never inferred after row materialization.

For a source component whose typing constraints and complete interface graph
are exactly represented by a finite formula `K_C` in these row relations,
present its fixed-environment scheme by the relation

```text
Inst_C(ρ) = { (ν,I) | ν assigns component-owned β ∧ K_C(ρ,ν,I) }
```

If `K_C` is sound and complete for that fragment's derivation relation and
records every observable root/use view, then `Inst_C(ρ)` equals the complete
derivable interface relation. It is therefore principal in the extensional
interface preorder: it contains every derivable instance and introduces
none. A direct corollary is that an existential row match with two
incomparable branches remains principal when retained as a disjunction;
replacing it with either conjunctive branch loses a derivable instance.

For example, inclusion of `{F<int>}` in `{F<α>,F<β>}` denotes
`(α ≈ int) ∨ (β ≈ int)`. The formula is finite and preserves both solutions.
The current evidence does not establish that this fragment covers ordinary
Yulang source constraints, that all component constraints admit such a finite
formula, or that evaluating/generalizing the formulas is terminating. It
also does not cover interval or compound arguments, handlers with
assignment-dependent route/coverage, or recursive SCC closure. It is a local
representability/principality result conditional on exact source-rule
generation, not yet the successor scheme theorem.

### Independent external uses versus internal SCC references

The constrained presentation gives a direct product lemma for independent
external uses. Let `u` range over semantic instantiation events as defined
by the source scheme rule, not over member names by assumption. Each event
selects a published scheme relation `S_u`; a single-member view can be
indexed by root `d_u` and scheduler version `v_u`:

```text
S_u(ρ) = Inst_{C,d_u,v_u}(ρ)
      = { (ν,I) | K_{C,d_u,v_u}(ρ,ν,I) }
```

If one source instantiation event exposes a tuple of member roots, `S_u` and
`I` are that joint relation and complete tuple; use one renaming for all of
it. Do not split such an event into per-member factors. Determining whether
the source rule instantiates one root view or a group is a source-semantics
obligation.

Assume the source scheme rule gives each external use an independent instance
of its selected relation. For every use `u`, let `ι_u` be one injective,
capture-avoiding renaming of all locally owned identities in the complete
interface and formula, fixing the same rigid `ρ`. Require the ranges of the
`ι_u` to be pairwise disjoint. The unconstrained joint relation is:

```text
Joint_U(ρ) = { ((ν_u,I_u))_u | (ν_u,I_u) ∈ ι_u(S_u(ρ)) for every u }
```

It has the equivalent finite presentation

```text
K_U = ⋀_u ι_u(K_{C,d_u,v_u})
```

over the disjoint union of the local identity ranges and the one shared
outer assignment `ρ`. Proof in each direction is restriction/union of
assignments: a joint assignment satisfies the conjunction exactly when its
restriction to every disjoint use namespace satisfies that use's renamed
`K_{C,d_u,v_u}`. Since each selected formula includes typed-family relations
and incidence, the product duplicates those together with each selected root
view; it does not share their local identities across uses. A caller
constraint `K_ctx` may relate copies, but it intersects with `K_U` only after
the independent instances exist.

Internal SCC references are different because the live component relation
already contains all mutually recursive roots and their shared graph. They
remain references inside that live relation and receive no `ι_u` per recursive
edge. The product factors only over distinct semantic instantiation events
that the source rule treats independently, not over SCC members or internal
calls. This is the relational form of open live-root sharing inside a
component and independent freshening at its boundary.

This proves the product equation only if the source generalization rule gives
each external use an independent instance and correctly classifies all free
outer anchors. It does not prove that the source builds any selected
`K_{C,d,v}` exactly, that the constrained formula solver terminates, or that
root-scheduler mutations are captured by the component relation. Those are
still required for the intrusion redesign's Oracle-capability theorem.

Frozen Oracle event characterization (not a successor rule): the SCC machine
receives `UseResolved { parent, target, use_value }` for one resolved reference
or one resolved selection. An unresolved intra-component use becomes an
`OpenUse` linking that occurrence's `use_value` to the target's live root. A
use of an already quantified target becomes one `InstantiateUse` event, which
selects that target's scheme and freshens it once. Adjacent instantiate events
may be grouped for constraint insertion, but the batch still prepares one
target scheme instance per event; the batch is an execution optimization, not
a shared multi-root instantiation. This supports root-indexed external use
views for those frozen event paths. It does not establish the successor's
source-level instantiation unit: the unified relation must derive that unit
from the source generalization/use semantics, and imported schemes or any
other source construct that exposes multiple roots need separate examination.

The product equation applies to the selected published relations; it does not
establish that all SCC member schemes come from one identical component
snapshot. The source audit recorded in
`notes/design/2026-09-29-intrusion-abstract-semantics-draft.md` found
root-preparation mutations and saved root results that later bounded passes
may not restart. If root `d` observes a particular generalized state version
`v`, use `Inst_{C,d,v}(ρ)` for that scheme relation. The product lemma applies
to a family of fixed `(d,v)` relations after their meanings are established.
Proving that these root/version views are projections of one `Rel_C`, or else
preserving their versioned simulation relation, remains a scheduler-simulation
obligation. The version label records machine history; it is not an
additional source-level selector.

## Relation operations and bookkeeping

The intended conceptual economy can be stated without one semantic operation
per source site. Starting from the source-defined complete relation, use
predicate restriction, relational composition/image, projection over owned
coordinates, and capture-avoiding reindexing:

| Mechanism | Relational operation | Required side condition |
| --- | --- | --- |
| Type or typed-family premise | Restrict the fiber by its symbolic predicate | Keep the predicate attached to every dependent interface coordinate |
| Callback/application | Compose caller, callee, and callback relations on the shared value/effect interface | Join at one valuation and preserve strict versus delayed execution |
| Typed row filter | Restrict the request coordinate by a predicate on the complete typed request | Route and activation facts are not inferred from the row predicate |
| Shallow handler | Relational image of continuation-bearing computations | Apply the source transition at each activation; require totality only for a claimed total transfer |
| Residual effect | Project the output request coordinate of that image | Do not replace the image by row difference without an equivalence proof |
| Generalization | Project component-owned coordinates while fixing imported `ρ` | Preserve the complete root/interface fiber and independent-use product law |
| Fresh instantiation | Reindex owned coordinates by one fresh injective map | Map request arguments, formulas, incidence, and boundaries together |
| Intrusion | Reindex the component relation along the parent map | Injective transport uses equivariance; non-injective maps require quotient/fiber preservation |

Row union is union on the request-support coordinate after forming the joint
relation. It is not relational disjunction between whole interfaces. Splitting
a row is a coordinate view of the same relation; existentially dropping a
shared binder is valid only when it is local to the projection and no retained
root, request, handler, or future-use observation depends on it.

In this account, `Sel_s` is a derivation witness for membership or inclusion;
`Demand` is an incidence edge used to compute a projection; typed-family
evidence is the predicate plus its fiber dependency; route evidence witnesses
the concrete handler transition; and transport maps reindex the relation.
These remain useful implementation records but add no mathematical construct.
If two source situations need different behavior after every complete
interface coordinate has been fixed, that signals a missing coordinate to
identify before adding a site-specific rule. This is a design diagnostic, not
a proof that the current interface carrier is complete.

#### Finite request-origin closure as a presentation, not a second semantics

The finite `Slot × Origin` / request-template closure recorded in the
progress note is admissible only as a finite presentation of the same
source-derived computation/interface relation. Its producer sites, slots,
owner IDs, and edge witnesses are indices used to construct and solve that
presentation; they are not new source-level effect constructors or extra
coordinates in `Rel_C` merely because the finite algorithm needs them. The
mathematical meaning remains the typed request behavior and complete
value/activation/continuation interface represented by `Rel_C`.

In particular, source calls, thunk forcing, continuation resumption, stores,
and handler transitions must all be instances of the same source computation
relation. The finite closure is a candidate abstraction/least-fixed-point
presentation of its reachable interface projection. A proof must give an
abstraction map and show each concrete step is simulated, while preserving
symbolic family predicates and their owner incidence. Unknown abstract targets
may widen the projected support to `Top`; widening is an abstraction choice,
not a special source rule. Handler subtraction still has to follow from the
relational handler image and its coverage proof, not from deleting an origin
or request template in the closure.

This restriction resolves an economy risk in the product-powerset sketch:
finite `ReqTpl` facts may be an efficient solver representation, but they
cannot become an independent semantic effect language parallel to `Rel_C`.
If the finite closure cannot preserve the complete relation's typed fibers,
it is an insufficient presentation; it does not justify a new site-specific
obligation. The next proof target is therefore a commuting abstraction
diagram from source steps through this finite presentation to the existing
relational operations, including filter, handler image, fixed-outer
generalization, fresh reindexing, and intrusion.

##### Conditional least-closure lemma

The fixed-point part of that target can be isolated from the source-specific
abstraction proof. Let `Conf` be the concrete configurations of the chosen
resumable source machine and let `→` include every permitted transition,
including store updates, thunk force, call, resume, handler arm selection,
and forwarding. Let `A` be a complete lattice of finite presentations ordered
by denotation inclusion; its coordinates must include the symbolic typed
family predicate and its incidence with every affected view. Let
`α : P(Conf) → A` and `γ : A → P(Conf)` form a Galois connection
(`α` and `γ` monotone, with `α(X) ≤ a` iff `X ⊆ γ(a)`). Write `Post(X)` for
all one-step successors of `X`, and let
`F(a) = α(I) ⊔ α(Post(γ(a)))`, where `I` is the set of admitted initial
configurations. Assume `F` is monotone and that the carrier/order treats
formula reindexing and typed-fiber preservation extensionally, rather than
discarding a formula when its current support projection is empty.

If the least fixed point `μF` exists, every finite concrete execution from `I`
is represented by it:

```text
Reach*(I) ⊆ γ(μF)
```

Proof: `α(I) ≤ μF` by the fixed-point equation. If a configuration `c` is
represented by `μF`, then `c ∈ γ(μF)`, so each successor `c'` contributes to
`Post(γ(μF))`; by construction `α(c') ≤ F(μF) = μF`, hence
`c' ∈ γ(μF)` by the adjunction. Induction on finite path length gives the
inclusion. By Tarski leastness, `μF` is below every `F`-pre-fixed abstract
state. Moreover, the adjunction makes these exactly the abstract states whose
concretizations contain `I` and are closed under `Post`: if `a` has those two
properties, then `α(I) ≤ a` and `α(Post(γ(a))) ≤ a`, hence `F(a) ≤ a`; the
converse follows by adjunction as well. Thus `μF` is the least closed sound
presentation in this abstraction.

This lemma does not establish an abstract machine for Yulang. The candidate
has not supplied `A`, `α`, or `γ` with these properties, and symbolic formulas
over potentially unbounded type identities may make `A` non-finite or fail
complete-lattice closure. More critically, `α(Post(γ(a)))` must be
effectively representable and monotone while retaining typed-family fibers;
merely collecting request templates or may-support is insufficient. Any
widening to `Top` is sound only if its concretization covers the concrete
successor and keeps all symbolic constraints required by other interface
coordinates. Finally, least closure proves principality only for this abstract
reachability component. The source typing relation, complete interface
projection, generalization/use product, and parent quotient must still show
that this least abstract closure is exactly the least representable
well-typed interface, with no lost or invented program acceptance.

The commuting-diagram gate can therefore be tested in two independent parts:

1. establish the abstraction simulation and monotonic finite transformer for
   each source transition class; this discharges reachability soundness and
   within-abstraction leastness;
2. establish that the type/effect derivation relation and its full SCC
   lifecycle are represented exactly by the resulting interface fibers;
   this discharges inference soundness and principality.

Passing part 1 cannot be cited as evidence for part 2. In particular, it does
not permit dropping a symbolic family constraint during solving,
residualization, generalization, freshening, or intrusion.

## Open gates

This draft does not yet define the supported source semantics or prove the
carrier adequate. Before a successor contract or implementation, establish:

1. declarative source computation, callback, thunk, and shallow-handler
   relations, including activation-specific visibility;
2. sound may-row and typed-family denotations whose symbolic invariance
   survives solving, residualization, generalization, instantiation, and
   intrusion;
3. a finite terminating principal presentation and its relation to the
   carrier;
4. SCC/root closure and parent-map preservation for the declared source
   envelope;
5. explicit counterexample search for repeated pushes/one pop, nested
   frames, complete and incomplete handlers, and residual effects;
6. final well-typed-program acceptance comparison over the supported envelope.

Method selection, roles, and implementation resolution remain a later
mandatory gate. Begin that gate only after ordinary effect and handler
semantics are settled, unless a concrete dependency appears earlier.
