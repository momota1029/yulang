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

The meaning of typed request inclusion and the source rule that creates a
shared invariant argument group still need definition. The core does not
assume that support inclusion, common-witness compatibility, and handler
eligibility are the same predicate. They are observations of different
coordinates in the same coupled relation: request denotation, symbolic type
admissibility, and dynamic boundary visibility respectively.

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
