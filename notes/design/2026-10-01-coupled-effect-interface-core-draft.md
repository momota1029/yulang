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

The component meaning is one extensional relation over assignments and
source-observable root interfaces:

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
`(ν,O)` pairs; `K` contributes by formula satisfaction, while `D` records how
the implementation preserves formula-to-view dependencies. Thus `K` is a
symbolic presentation of a semantic restriction and `D` is transport
bookkeeping, not part of the mathematical carrier. A post-solve or
post-handler presentation must denote the required transformed relation. If
a formula is discharged, the proof must establish equivalence for the
affected views; equality of materialized rows is not such a proof.

The meaning of typed request inclusion and the source rule that creates a
shared invariant argument group still need definition. The core does not
assume that support inclusion, common-witness compatibility, and handler
eligibility are the same predicate. They are observations of different
coordinates in the same coupled relation: request denotation, symbolic type
admissibility, and dynamic boundary visibility respectively.

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
  and eligible at the relevant activation. The route evidence is a genuine
  coordinate of the relation, not a row selector.

These descriptions are a common denotational interface, not a claim that each
operation is a homomorphism. In particular, a handler may fail to preserve
union exactly because a may-row forgets correlations between requests and
continuations. Soundness requires an over-approximation of the relational
image; principality asks for the most-general representable result in the
chosen interface language.

#### Formulation choice and semantic/bookkeeping boundary

There are three plausible presentations of this same design problem:

| Candidate presentation | Conceptual economy and composition | Principality and proof reuse |
|---|---|---|
| A separate selector/obligation rule at each source site (`Sel_s`, `Demand`, typed-family pair obligations, and route-transfer cases) | Easy to attach to current solver events, but duplicates the meaning of row comparison, callback invocation, handler residualization, and variable transport. A new source form tends to need another rule. | Local checks can be executable, but their joint solution relation and cross-site preservation must be reconstructed. Proofs do not compose automatically. |
| A ground may-support row plus a separate provenance/route analysis | Small support algebra and a finite least-support candidate; operational visibility remains explicit. | Support alone forgets valuation, result/request, and continuation correlations. Separate analyses need a proved coupling, and handler images need not distribute over row union. This can be a derived coarse solver view only when the coupling theorem holds. |
| One assignment-indexed relation over complete root, typed-request, ownership, and visibility observations | One relation composes source evaluation, callbacks, and handler transitions; row splitting/filtering and lifecycle maps are projections or images. | Preserves correlations needed for principality and reuses image/transport lemmas, but may not have an effective finite principal presentation. That is an open theorem, not a reason to add site-specific semantic rules. |

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
remain observations and do not invent a result. A case expression then has
the sequencing equation

```text
Run_ν(case e of arms,η,s) =
  Run_ν(e,η,s) >>= (λ(v,η',s'). Match(v,arms,η',s'))
```

`Match(v,arms,η,s')` tests patterns in source order using one pattern-binding
relation and extends `η` with successful bindings. Pattern binding includes
conditional field-default evaluation; a default request and its continuation
remain in the relation. For each matching pattern, it evaluates the guard,
if present, under the resulting environment and dynamic state; a false guard
continues with the next arm, and a true or absent guard evaluates that arm's
body. A guard request and its continuation remain in this same
state-threading relation. For any observation relation `R`, define collected
typed-request support at fixed assignment `ν` by

```text
MayReq(R,ν) = ⋃ { typed_requests(τ) | (τ,o) ∈ R at assignment ν }
```

Let `Ret*(R)` be returns reached from `R` along every well-typed finite
resumption of its saved continuations, where resume values are admitted by the
operation signature and active handler/source context. Retain each returned
value, environment, and dynamic state. Define the reachable match image

```text
MatchImg(R,arms) = ⋃ { Match(v,arms,η',s') | (v,η',s') ∈ Ret*(R) }
```

Thus requests emitted while evaluating the scrutinee precede matching, and
requests from attempted guards and the selected body follow in order. The
source rule needed for the frozen `file::load` fixture is that a case
scrutinee typed as an effectful computation uses `Run_ν` and composes its
computation before matching. The fixture plus frozen runtime behavior
supports this candidate reading, but current Y3 has no authoritative typing
rule proving it. Current mono emission omits an explicit `ForceThunk`, and the
evaluator supplies the demand at runtime.

For fixed `ν`, the equation yields the sound support bound

```text
MayReq(Run_ν(case e of arms,η,s),ν)
  ⊆ MayReq(Run_ν(e,η,s),ν)
   ∪ MayReq(MatchImg(Run_ν(e,η,s),arms),ν)
```

because bind either retains a scrutinee request or composes the reachable
continuation/return into `MatchImg`. That image includes pattern-bound
environments, conditional defaults, attempted guards, false-guard fallthrough,
and selected bodies at their actual dynamic states. The complete relation
preserves which arms were reached and result/request correlation. This
inclusion is a consequence of the candidate stateful bind equation, assuming
`Ret*` ranges over all permitted typed resumptions. It does not establish a
principal row rule.

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

A compact candidate gives ordinary Function types a relational reading. Let
`Beh_{ρ,ν}(f,x)` be the source-defined relation of finite evaluation
observations from applying callable value `f` to argument value `x`. Each
observation is a pair `(τ,o)`, where `τ` is a finite typed-request prefix and
`o` is either `Return(v)` for a completed call or `Prefix` when evaluation has
not yet returned. Include every finite prefix, including prefixes of runs that
eventually diverge, so an emitted request is still checked when there is no
return value. A returned value records its latent interfaces. Whether delayed
requests belong to `τ` or only to a returned latent interface must follow the
source thunk/force rules; `Beh` does not assume that boundary. Write
`supp_now(τ)` for the **typed-request** support observed at the source-defined
call boundary, retaining each family argument. Then a candidate denotation is:

```text
f ∈ ⟦A ->[E] B⟧_{ρ,ν} iff
  ∀x ∈ ⟦A⟧_{ρ,ν}.
  ∀(τ,o) ∈ Beh_{ρ,ν}(f,x).
    supp_now(τ) ⊆ TypedRow(E,ν) ∧
    (o = Return(v) ⇒ v ∈ ⟦B⟧_{ρ,ν})
```

Define semantic Function compatibility by inclusion between these denotations.
Application composes callee evaluation, argument evaluation, and `Beh`; a
surrounding handler acts on the resulting complete computation relation. A
finite structural rule is a sufficient compatibility condition: formal
arguments are admitted by the actual domain, actual results fit the formal
result, and `RowSub(E_actual,E_formal,ν)` holds, if the source semantics
establishes that `E` bounds these call-boundary requests. This yields the usual
argument contravariance, result covariance, and effect inclusion in the safe
direction. For fixed `Beh`, the direct proof is: every value admitted by
`A_formal` is admitted by `A_actual`; each observed result in `B_actual` is
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
define `supp_now`, delayed operations/thunks, callback invocation, and
nonreturning prefixes in one evaluation relation; neither Oracle routing nor
the pure F5 Function rule settles them.

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
and request visibility evidence. At the semantic level, a request and an
activation are related by one `Visible(q,κ)` judgment; it determines whether
that activation handles or forwards the request. This coordinate is needed
because it changes observable behavior. The runtime-guard contract represents
it with request-carried guard identities and the active stack, and defines
`add_id` coloring from an entry snapshot. The frozen evaluator also carries a
`handler_boundary` field. These concrete forms are implementation witnesses
for `Visible`, not separate inference rules or mathematical constructs. A
current-stack-only predicate is therefore incomplete. The specifications
give these cases:

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
uses `Visible(q,κ)` for routing; the evaluator's concrete guard fields and
`handler_boundary` remain implementation evidence, not additional inference
rules. No soundness or final-acceptance claim follows until these simulation
obligations are closed.

This anchor does not decide which source expressions specialization must
lower to `MakeThunk` or `ForceThunk`, nor does it prove that Function effect
annotations denote upper bounds of the immediate observations. Those remain
static source-adequacy obligations. In particular, the inference relation
must predict every runtime thunk boundary without consulting the frozen
Oracle's weight routing.

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
relation; it is not calculated from a family row alone. The totality predicate
below requires a transition for every computation in the represented fiber;
typing that covers only an existential subset does not justify this universal
abstraction.

For an interface relation `R` over owned valuations and root interfaces, let
`P_{H,κ,ρ}(ν,I)` be the totality predicate of the *declarative typed
transition relation* for this handler at activation context `κ`, under fixed
imports `ρ`, and complete input interface `I`. It contains exactly the source
typing premises needed to make the transition well-typed; it is not a selector
or separate obligation kind added for this source site. In a finite
presentation, its formula is conjoined to the existing `K` before the handler
image/residual support is formed. Define
`R_{H,κ,ρ} = { (ν,I) ∈ R | P_{H,κ,ρ}(ν,I) }`, its concrete fiber, and the
least semantic output relation:

```text
C_ρ(R_{H,κ,ρ}, ν) = ⋃ { C_ρ(I,ν) | (ν, I) ∈ R_{H,κ,ρ} }

H#_κ(R) = { (ν, J) |
    there are I, c, c' with (ν, I) ∈ R_{H,κ,ρ}, c ∈ C_ρ(I,ν),
    Step_{H,κ,ρ}(ν,I,c,c'), and J ∈ Obs_H(I, ν, c') }
```

To make the common relational core explicit, `P_{H,κ,ρ}` should be derived from one
typed source transition relation rather than generated as an independent
handler-side predicate. Write
`Step_{H,κ,ρ} ⊆ { (ν,I,c,c') | c ∈ C_ρ(I,ν) }` for the declarative
shallow-handler step at the fixed activation, including operation identity,
family argument, payload/result, and activation eligibility premises. Then

```text
P_{H,κ,ρ}(ν,I) iff ∀c ∈ C_ρ(I,ν). ∃c'. Step_{H,κ,ρ}(ν,I,c,c')
```

and `H#_κ` is the image of this context-indexed relation followed by the
common observation map, ranging over every represented `c`. The notation
`P_{H,κ,ρ}` is only the totality predicate derived from this relation and
needed to state the fiber theorem; it is not another semantic construct. This
also identifies the proof boundary: a source rule that cannot be stated in
`Step_{H,κ,ρ}` without a source-site selector would expose a genuinely missing observable coordinate
or refute this candidate's claimed unification.

Here the complete observation includes output values with their latent
interfaces, typed request facts, family-argument denotations, occurrence
ownership, and route lineage. The finite presentation is separate: if
`p=(V,M,Q,K,D)`, its handler transformation must carry every formula in `K`
through its endpoint substitution and map its incidence `D` to the dependent
output views. A formula may leave the new presentation only with proof that
its meaning is preserved for every dependent output view. New operation,
arm, or route predicates enter `K` from the typed source transition before
the presented support row changes. Observing concrete `c'` alone cannot
reconstruct this presentation proof.

The relation keeps `ν` fixed during transfer, so this image cannot validate a
typed-family condition only after erasing its symbolic endpoints. The induced
support view is the may-row effect of the handler. No `Drop` operation is
part of this definition. The collecting support projection below deliberately
states only ground support soundness and leastness; it does not prove that a
finite presentation transports `K,D` correctly.

The handler image has a useful fiber-domain criterion. If each `I` in
`R_{H,κ,ρ}` has a represented concrete computation and the handler plus
symbolic observation are total on those fibers, then:

```text
dom_ν(H#_κ(R)) = dom_ν(R_{H,κ,ρ})
```

For the forward inclusion, an element of `H#` supplies its input `(ν,I)`,
which must satisfy `P_{H,κ,ρ}`. For the reverse inclusion,
choose the represented computation guaranteed by nonemptiness and apply the
total transition and observation to obtain an output at the same `ν`. This
locates any legitimate assignment restriction at the declarative handler
premises. It cannot arise later because row materialization or residual
support dropped a symbolic formula. For a handler transition whose source
premises are already entailed by `R`, the criterion reduces to preservation
of the whole input valuation domain.

**Conditional transfer theorem.** If (1) `C_ρ(I,ν)` covers every concrete
scrutinee represented by each `(ν,I) ∈ R_{H,κ,ρ}`, (2) `H_κ` is total on those
fibers and agrees with the source shallow-handler transition, and (3) `Obs_H`
is a sound output observation, then `H#_κ(R)` is sound: every concrete handled
result represented on an input fiber is represented on the corresponding
output fiber. Moreover, among exact relations over the chosen
complete-interface carrier, `H#_κ(R)` is the least sound relational image:
any relation containing the observation of every such `H_κ(c)` must contain
`H#_κ(R)`. This is leastness for the semantic transfer, not a proof that the
image has a finite formula, that a solver computes it, or that the whole type
inference system is principal. Finite-presentation `K,D` transport is a
separate open correctness lemma, not a semantic premise of the image.

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

Whenever a request is matched to an arm, one source operation-signature
relation checks operation identity, invariant family arguments, and
payload/result compatibility. Forwarding carries the existing request
constraints unchanged. The handler's selection determines which computation
relation runs; it does not choose a different family-argument comparison.
Route eligibility remains a separate coordinate of the same source relation.

For one exact operation declaration with request instantiation `θ` and arm
instantiation `φ`, the local value-safety premises have the following
conditional form:

```text
same OpId
family_relation(F<θ(ρ̄)>, F<φ(ρ̄)>)
Aθ <: Aφ
Bφ <: Bθ
```

Here `op : ∀b̄. A -> [E] B` and `F<ρ̄>` is the declaration's family
projection; `ρ̄` need not contain every operation binder. The family relation
is the chosen symbolic invariant-argument meaning, retained in `K`; the two
value inequalities include every operation-only binder that occurs in the
payload or result. The payload premise lets the arm consume a request value,
and the resume premise lets the request's raw continuation consume any value
the arm supplies. This follows from the shallow boundary where the arm gets
the raw continuation. The argument is conditional on the subtype/coercion
relation being sound for runtime values and on the exact operation declaration
being the same on both sides. It does not assign ownership to `Eθ`/`Eφ`,
select a route, or determine when this arm is eligible; those remain in the
same complete transition relation. Thus these are premises of
`P_{H,κ,ρ}`, not an
additional per-operation obligation kind. The full source rule and
principality of its finite presentation remain open.

The family predicate alone is insufficient even in a closed point case. Let
`F<>` have no family arguments and let the request payload be `Bool`, while
the arm expects `Int`. `family_relation(F<>,F<>)` is vacuously true, but no
runtime-safe `Bool <: Int` payload transfer exists in the ordinary disjoint
base-type fragment. The pair must therefore fail the complete
`P_{H,κ,ρ}` relation;
support-head equality cannot justify consuming it. This
is a test of the unified operation relation: payload/result behavior is
already part of the same transition, not a new family-specific selector.

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

The pointwise law lifts to the complete relational image. Define the
factor-assignment reindexing
`σ^*R = { (ν',T_σ(O)) | (σ*ν',O) ∈ R }`. Assume the concretization,
transition-domain predicate, and output observation are natural under the
same map:

```text
C_ρ(T_σ(O),ν') = T_σ[C_ρ(O,σ*ν')]
P_{H,κ,ρ}(ν',T_σ(O)) iff P_{H,κ,ρ}(σ*ν',O)
Step_{H,κ,ρ}(ν',T_σ(O),T_σ(c),T_σ(c'))
  iff Step_{H,κ,ρ}(σ*ν',O,c,c')
Obs_H(T_σ(O),ν',T_σ(c'))
  = T_σ[Obs_H(O,σ*ν',c')]
```

Then the relational handler image satisfies:

```text
σ^*(H#_κ(R)) = H#_κ(σ^*R)
```

Each side is generated by the same reindexed witnesses `(O,c,c')`. The
pointwise transition lemma above supplies the `Step` witness equation; the
other identities map input validity, concrete computations, and output
observations. These assumptions map witnesses in both directions. This is
exact on assignments factoring through `σ` and proves that handler
residualization can transport symbolic
family constraints through a solve step without reconstructing them from the
output row. It still does not show that all source solutions factor through
`σ`, nor that the output has a finite principal presentation.

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

### Exact criterion for a non-injective parent quotient

Let `P` fix outer identities and map owned identities to parent identities,
possibly identifying several owned identities. Define the quotient only by
direct substitution through the complete formula and interface:

```text
K_P(ρ,μ) = K_C(ρ, μ∘P, I[P])
```

Every satisfying quotient assignment `μ` lifts to the source assignment
`μ∘P`, so this construction cannot add source solutions. It can remove
solutions: it keeps only assignments that are constant on every fiber of
`P`. Let `Obs_C(ρ,ν,I)` be the complete external observation chosen for
principality, including every projected root and the typed request/handler
behavior clients may constrain. The quotient preserves the source relation
exactly up to that observation iff:

```text
for every (ν,I) satisfying K_C(ρ), there exists μ such that
  K_P(ρ,μ) and
  Obs_C(ρ,ν,I) ≈_Obs Obs_C(ρ, μ∘P, I[P]).
```

The forward direction is exactly the condition that every source observable
has a `P`-constant representative; the reverse direction follows from the
lifting property above. This is necessary and sufficient for the direct
quotient construction, but not by itself a practical solver test: both the
source relation and the complete future-client observation must be defined.
The point-fragment entailment condition below is a tractable sufficient
criterion for one chosen `≈_Obs`; `FamAgree_A` alone fails the exact criterion
for the interval counterexample that follows.

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
