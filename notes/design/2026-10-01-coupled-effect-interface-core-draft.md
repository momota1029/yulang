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
view observable by clients. A computation view contains:

- a may-bound on typed requests;
- symbolic request arguments and operation payload/result constraints;
- occurrence and owner incidence needed by future generalization;
- origin and boundary lineage needed to determine handler eligibility.

The component meaning is one relation:

```text
Rel_C(ρ) ⊆ { (ν, I) | ν assigns β and I is a complete root interface }
```

The relation couples roots, request views, symbolic constraints, owners, and
routes. A row, obligation ledger, or dependency edge is a finite presentation
or projection of this relation. None is the semantic authority separately.
In particular, a typed-family invariant remains a predicate over symbolic
argument endpoints and the source-derived shared occurrence identity inside
`Rel_C`; solving may substitute its endpoints or discharge it with proof, but
materialized row comparison cannot recreate it after it has been dropped.

For transport statements, write a presented interface as
`I = (V, M, Q, K, D)`: value views `V`, may-support coordinates `M`, typed
request facts `Q`, symbolic formulas `K`, and incidence `D` connecting each
formula to the views that depend on it. This tuple is a presentation of an
element of the carrier, not five independent semantic authorities. A
post-solve or post-handler presentation must carry `K` and `D` forward. If a
formula is discharged, it must carry a proof of equivalence for the affected
views; equality of materialized rows is not such a proof.

The meaning of typed request inclusion and the source rule that creates a
shared invariant argument group still need definition. The core does not
assume that support inclusion, common-witness compatibility, and handler
eligibility are the same predicate. They are observations of different
coordinates in the same coupled relation: request denotation, symbolic type
admissibility, and dynamic boundary visibility respectively.

#### One denotational row relation (candidate)

For a fixed type/row assignment, interpret a typed row jointly with its
source-owned family-instantiation binders. Let `g(o)` identify the already
owned type binder or binder tuple whose invariant argument is shared by
occurrence `o`; it is not a fresh semantic variable added solely for row
matching. Occurrences with no shared binder receive distinct local identities.
This identity comes from lexical/source ownership and is transported with the
complete relation, not selected by a row-comparison call site. If
`ArgDen_A(o,ν)` interprets the complete argument tuple of occurrence `o`,
define the joint typed-request relation:

```text
J_R(ν) = { (b, Q) |
  b_g ∈ ⋂_{o:g(o)=g} ArgDen_A(o,ν) for every binder g,
  Q = { (head(o), b_{g(o)}) | o ∈ occurrences(R,ν) }
}
TypedRow(R,ν) = { q | ∃b,Q. (b,Q) ∈ J_R(ν) ∧ q ∈ Q }
RowSub(R,S,ν) iff J_R(ν) ≠ ∅ ∧ J_S(ν) ≠ ∅
                   ∧ TypedRow(R,ν) ⊆ TypedRow(S,ν)
```

Open tails are evaluated in the same assignment before taking this relation;
they are not replaced by a second source-site rule. `RowSub` is the candidate
meaning behind row splitting, filtering, and row comparison. A solver may
expand subset into finite witness formulas, but a `Sel_s`/`Demand` pair list
then records a derivation of membership, not an additional semantic choice.
For singleton point arguments with independent binders, the expansion is the
familiar per-left-occurrence disjunction over compatible right occurrences.
For interval or compound arguments, the set denotation controls the expansion
and preserves shared tuple dependencies; pairwise overlap is not assumed
equivalent. The nonempty-`J` premise also prevents an inconsistent shared
binder from making inclusion vacuously true by projecting to an empty row.

The common-witness condition is now a projection of `J_R`: a row assignment
admits a typed request view exactly when every shared binder has a witness in
the intersection of its occurrences' argument denotations. Typed-family
invariance is therefore not a second obligation kind; it is the nonempty-fiber
condition for this joint relation. If the source does not establish shared
ownership, there is no shared binder and no intersection is imposed. Both
row inclusion and family coherence are observations of `J_R`, not facts
reconstructed from materialized family-head support. Handler eligibility
remains a property of the source handler transition on typed requests and
active boundaries, not a variant of `RowSub`.

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
split, their joint assignment factors and:

```text
TypedRow(R ∪ S,ν) = TypedRow(R,ν) ∪ TypedRow(S,ν)
```

If the split separates occurrences that share a binder, the equality may be
strict. Let their argument denotations be `{int,bool}` and `{bool,str}`. The
whole relation permits only the common witness `bool`; projecting the two
pieces independently admits `int` and `str` as well. The relational split
therefore carries the original binder and its full incidence; a solver may
factor it only after proving the factorization condition. This is a direct
criterion for when row splitting is a harmless view and when it would lose a
typed-family constraint.

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
`GroupEq(R)` to require this equality for every pair of occurrences sharing
one binder in `R`. Then:

```text
RowSub(R,S,ν) iff
  GroupEq(R,ν) ∧ GroupEq(S,ν) ∧
  ⋀_{o∈occurrences(R)} ⋁_{p∈occurrences(S), head(p)=head(o)}
      args(o) ≈ args(p)
```

An empty disjunction is false. `GroupEq` is exactly nonemptiness of each
point-valued binder fiber in `J`; after it holds, `TypedRow` is the finite set
of typed requests carried by the occurrences. The final conjunction is then
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

#### Finite-domain coverage and why one selected match is insufficient

For a fixed assignment, suppose each argument denotation is a finite subset of
a finite carrier `U`. Then the same set-inclusion relation has the exact
expansion:

```text
RowSub(R,S,ν) iff J_R(ν) ≠ ∅ ∧ J_S(ν) ≠ ∅ ∧
  ⋀_{q∈TypedRow(R,ν)} ⋁_{p∈TypedRow(S,ν)} q = p
```

This is a finite formula over typed requests; it needs no distinguished
left/right occurrence pairing. A useful boundary case has one left occurrence
whose argument denotation is `{int,bool}` and two right occurrences whose
denotations are `{int}` and `{bool}`. Inclusion holds because their union
covers the left denotation, although neither right occurrence covers the
whole left occurrence by itself. A solver that commits to one right partner
per left occurrence loses this valid solution. Conversely, pairwise overlap
alone is insufficient: for left `{int,bool,str}` and right `{int}` plus
`{bool}`, each right occurrence overlaps the left, but `str` is uncovered.
The inclusion formula rejects that case.

The exact all-values formula for symbolic endpoints is
`∀q∈TypedRow(R,ν). ∃p∈TypedRow(S,ν). q=p`. A finite solver can eliminate
these quantifiers only when the selected type/argument algebra admits a
terminating exact coverage procedure. The relation itself remains unified
without such elimination, but its finite representation and principality do
not follow. This makes coverage, rather than choosing a source-site selector,
the concrete next proof obligation for interval-valued rows.

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
  and eligible at the relevant activation. The route evidence is a genuine
  coordinate of the relation, not a row selector.

These descriptions are a common denotational interface, not a claim that each
operation is a homomorphism. In particular, a handler may fail to preserve
union exactly because a may-row forgets correlations between requests and
continuations. Soundness requires an over-approximation of the relational
image; principality asks for the most-general representable result in the
chosen interface language.

### Handler transfer as a relational image

Let `C_ρ(I,ν)` be the set of well-typed continuation-bearing computations
represented by a complete interface `I` under the owned-variable assignment
`ν` and fixed imports `ρ`. It includes the values, captured environments,
latent function/thunk behavior, and activation lineage needed to interpret
later calls and forces. Let `H_κ` be
the source shallow-handler transformation at activation context `κ`. The
context includes the active handler stack and the source-defined visibility
relation; it is not calculated from a family row alone. Require `H_κ` to be
defined for every computation in `C_ρ(I,ν)`. If typing can establish only an
existential subset, the universal abstraction below is not justified.

For an interface relation `R` over owned valuations and root interfaces,
define its concrete fiber and the least semantic output relation:

```text
C_ρ(R, ν) = ⋃ { C_ρ(I,ν) | (ν, I) ∈ R }

H#_κ(R) = { (ν, J) |
    there are I, c, c' with (ν, I) ∈ R, c ∈ C_ρ(I,ν),
    c' = H_κ(c), and J ∈ Obs^sym_H(I, ν, c') }
```

Here the complete observation includes output values with their latent
interfaces, typed request facts, symbolic argument constraints, occurrence
ownership, and route lineage. Crucially, `J` is not reconstructed solely by
materializing `c'`: it includes the symbolic transport of the input
presentation. If `I = (V,M,Q,K,D)`, a symbolic handler step must provide a
map `τ_H` from input view identities to output view identities and carry every
formula in `K` through its endpoint substitution into `K'`. Its incidence
must be mapped through the same `τ_H`; formulas may leave `K'` only with
proof evidence that their meaning is preserved for every dependent output
view. New operation-signature, arm, or route constraints are generated at
their symbolic source relation before rows are changed. A path through
concrete `c'` alone cannot discharge these obligations.

The relation keeps `ν` fixed during transfer, so this image cannot validate a
typed-family condition only after erasing its symbolic endpoints. The induced
support view is the may-row effect of the handler. No `Drop` operation is
part of this definition. The collecting support projection below deliberately
states only ground support soundness and leastness; it does not prove this
symbolic interface-transport condition.

**Conditional transfer theorem.** If (1) `C_ρ(I,ν)` covers every concrete
scrutinee represented by each `(ν,I) ∈ R`, (2) `H_κ` is total on those fibers
and agrees with the source shallow-handler transition, and (3) `Obs^sym_H`
is a sound output observation that preserves the `K,D` obligations described
above, then `H#_κ(R)` is sound: every concrete handled result represented on
an input fiber is represented on the corresponding output fiber. Moreover,
among exact relations over the chosen complete-interface carrier,
`H#_κ(R)` is the least sound relational image: any relation containing the
symbolically transported observation of every such `H_κ(c)` must contain
`H#_κ(R)`. This is leastness for the semantic transfer, not a proof that the
image has a finite formula, that a solver computes it, or that the whole type
inference system is principal. The `K,D` transport premise is a separate open
lemma, not a consequence of the ground collecting support argument.

### Symbolic preservation at one shallow-handler step

The required `K,D` premise can be stated without adding another obligation
kind. Write `K` for the existing formulas in the coupled interface and `D`
for their dependency incidence. A source handler step partitions the
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

Whenever a request is matched to an arm, one source operation-signature
relation checks operation identity, invariant family arguments, and
payload/result compatibility. Forwarding carries the existing request
constraints unchanged. The handler's selection determines which computation
relation runs; it does not choose a different family-argument comparison.
Route eligibility remains a separate coordinate of the same source relation.

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

### Shared-witness formula under symbolic transport

The interval-valued family constraint has a direct transport law in the
candidate denotation already recorded in the effect proof notes. For a
source-derived indexed batch `B`, define

```text
FamAgree_A(B,ν) iff
  ⋂ { ArgDen_A(args(o),ν) | o ∈ B } ≠ ∅
```

Assume the chosen argument denotation is natural under a type substitution
`θ`, including its complete tuple dependencies:

```text
ArgDen_A(θ(args(o)),ν') = ArgDen_A(args(o),θ*ν')
```

Then substitution preserves the whole shared-witness formula:

```text
FamAgree_A(B[θ],ν') iff FamAgree_A(B,θ*ν')
```

Proof: apply the denotation identity to each indexed occurrence; the two
families of tuple sets are equal, hence so are their intersections and their
nonemptiness. This uses one intersection over the entire batch, so it
preserves cross-position and N-way dependence; it does not reduce the formula
to pairwise compatibility. A point-valued `InvArgs` encoding is a valid
replacement only when a separate theorem proves that it denotes this same
relation for the chosen arguments.

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

### Generalization and fresh use as abstraction and reindexing

This gives an exact lifecycle lemma without a special rule for typed-family
obligations. Let `Ω` be the complete set of identities owned by one frozen
component: type and row variables, request occurrences, shared-argument batch
identities, and locally bound handler/owner identities. Let `ρ` be the fixed
outer identities. Present the component by one predicate
`K_C(ρ,ω,I)`; `K_C` includes every source-derived family-invariance formula.
Generalization packages the pair `(Ω,K_C)` as a scheme template, binding the
owned identities and leaving `ρ` free. It does not evaluate `K_C` after
materializing rows or extract only the type-variable portion of `Ω`.

For one use, choose a capture-avoiding bijection `ι` from `Ω` onto fresh owned
identities, fixing `ρ`. Instantiate by reindexing the *whole* presentation:

```text
K_{C,ι}(ρ,ω',I') = K_C(ρ, ι⁻¹(ω'), ι⁻¹(I'))
```

where the inverse acts on every identity sort it owns and leaves fixed outer
identities unchanged. For each source assignment `a` and target assignment
`a'` related by `a'(ι(x)) = a(x)` for all `x ∈ Ω` and equal on `ρ`,
structural satisfaction gives:

```text
a' ⊨ K_{C,ι}(ρ,ω',I')  iff  a ⊨ K_C(ρ,ω,I)
```

The proof is induction on the formula and interface syntax. Atomic type and
row relations are unchanged under the corresponding reindexing; a
`FamAgree_A` atom has the same indexed family of argument denotations; and
conjunction/disjunction preserve equivalence componentwise. Therefore every
independent use gets an isomorphic satisfying fiber when it receives a
disjoint `ι`, while all uses retain the same rigid outer assignment. No
formula is regenerated from its materialized row. For an SCC's internal use,
there is no `ι`: its roots and formulas remain in the one live `K_C` relation.

This is exact for injective alpha-renaming and establishes the typed-family
lifecycle requirement across generalization and fresh instantiation at the
relational-presentation level. It does not prove that source lowering builds
the correct `K_C`, that a solver preserves it, that an implementation stores
all of `Ω`, or that non-injective solving/intrusion preserves fibers. Those
remain separate correspondence and quotient theorems; identity reindexing
cannot justify merging independent variables.

### A sufficient parent-quotient condition (point fragment)

There is a useful sufficient condition for non-injective intrusion that is
stronger than the substitution pullback identity. Let `P` map the component's
exported type-variable identities onto parent identities, extending `P` by
identity on component-local identities that are not intruded, and let
`K_C(ρ,ν,I)` be the exact finite point-fragment relation. Let `μ` assign the
boundary parent identities while `ρ` stays fixed. Define its quotient
presentation by direct substitution:

```text
K_P(ρ,μ,I) = K_C(ρ, μ ∘ P, I[P])
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
the value of its parent, and the definition of `K_P` makes that lift a source
solution. The observable interfaces agree modulo `≈` by premise 3. Thus this
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

### Finite point-row constrained presentation (conditional lemma)

There is a finite presentation candidate for the point-valued closed-row
fragment that avoids choosing an eager row match. For finite rows `R` and
`S`, define symbolic inclusion by:

```text
RowIncl_A(R,S,ν) =
  ⋀_{x ∈ R} ⋁_{y ∈ S, head(y)=head(x)} FamCompat_A(x,y,ν)
```

An empty disjunction is false. For point-valued family arguments,
`FamCompat_A` is the symmetric subtype-equivalence formula, under the
conditional premise that this equivalence is the source argument relation.
Every occurrence in the formula shares the same valuation `ν`; no disjunct
is selected while another branch remains possible. A finite row produces a
finite formula DAG, and repeated subformulas may be shared without changing
its denotation.

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
