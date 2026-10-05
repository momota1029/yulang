# Production Function inlet admission: Draft source clause and production gap

Date: 2026-10-05
Status: conditional source-call derivation and production-gap localization; no semantic rule, carrier, or implementation authority
Baseline: `2477d3730`
Scope: distinguish the Draft source-application clause from the unresolved production challenge-admission interpretation

## Result

The prior claim that no candidate source inlet clause exists was too strong.
The Draft typed-computation core §6 describes a source application
construction relating the whole `Result(I_a)` carrier to the Function
parameter interface, with typed path/contract obligations. The user's
endpoint-dependent `A <: B` decision supplies the intended shape of concrete
comparison resolution, but it does not by itself define the endpoint/path
translation for this Draft clause. Thus §6 is a bounded source-rule candidate,
not an established general admission judgment.

The production callback containment theorem remains open. Section 6 presents
a candidate source-generation shape; even if formalized, it would not be an
exhaustive production interpretation of challenge admission over the approved
complete `Rel_C` and fixed `(nu,K,D)` basis. Current production HIR does not
emit callback applications, and Option 2 permits production memberships
without source-constructor witnesses. The remaining gap is the exhaustive
production admission/satisfaction rule and full containment, not merely the
presence of a source-application shape.

Under the §6 Draft construction, a generated source application is described
as relating an argument's whole `Result(I_a)` carrier to the callee's parameter
interface while retaining typed path/contract evidence, source roots, and
shared dependencies. The subsequent entry behavior is also proposed to
preserve the selected distinction:

- A `Value(A)` parameter receives the whole carrier, forces its designated
  computation once at entry, rebinds the result, then enters the body and
  result consumer. Incoming carrier effects can be observable even when the
  body is pure.
- A retained `Computation(E,A)` parameter binds that same carrier without an
  entry force. Its body may explicitly consume it; its effects cannot be
  added to the call merely because the carrier was passed.

If the candidate endpoint/path translation is established, its local check
would be the ordinary endpoint-dependent inequality query with typed
path/contract evidence; it cannot be inferred from success of the pending
whole-Function comparison, body effect-purity, equal result types, `never`, or
effect-row support. The Draft source clause does not define admission roots for
arbitrary typed contexts or production-only members. The approved Option 2
policy permits non-source-witnessed production members, while still requiring
typed paths, authority, dependencies, and complete observation conditions.

Even if this source-call construction is formalized, production membership must define
the complete endpoint/role/path/origin/continuation/scope/authority/dependency
predicate over `Rel_C`, and prove
`D_C(xi) subseteq D_A(xi)` and
`forall c in D_C(xi). P_A(c;xi) subseteq P_C(c;xi)`.
This note narrows one input to that main gate; it does not claim the main
theorem is closed.

## Governing clauses and exact gap

The Draft source construction proposes a local application obligation and
role/entry behavior, but its exact inequality realization, the all-context
judgment, and production interpretation remain open:

- [Typed computation core §6](../design/2026-10-02-typed-computation-core-elaboration.md)
  gives an application synthesis shape and says the whole `Result(I_a)` is
  related to the parameter interface with typed path/contract obligations
  (lines 417–423). Reading that obligation as an `A <: B` query requires an
  endpoint/path translation that this Draft does not define. It does not
  define a separate admission relation for arbitrary production observations.
- [Typed computation core §9](../design/2026-10-02-typed-computation-core-elaboration.md)
  fixes Value-entry `Force; rebind; body; consumer` and retained-computation
  entry (lines 912–986). It explicitly separates `J_arg`, `J_body`, and
  complete `J_call`, so a pure body is not an inlet criterion.
- [Coupled interface core](../design/2026-10-01-coupled-effect-interface-core-draft.md)
  proposes a typed two-hole `CallCfg` that keeps the tested callable out of
  the context environment, avoiding direct self-membership circularity
  (lines 942–967), but leaves the exact typing judgment open at line 969.
- [Source-indexed callback realization §4](../design/2026-10-04-source-indexed-callback-realization.md)
  supplies comparison-independent admission for its finite decorated,
  source-generated reference challenges (lines 178–205). That bounded
  certificate does not define the general production inlet or cover every
  production-only member permitted by Option 2.
- [Approved production denotation](../../questions/2026-10-05-production-function-denotation/approved-answer.md)
  selects complete typed observations in the existing `Rel_C` fiber, with
  separate comparison-independent context admission. It explicitly leaves
  the concrete endpoint/admission clauses open.

The [direct complete-Function audit](2026-10-05-production-complete-function-interpretation-audit.md)
already localizes the wider missing predicates `Admit_F` and `Sat_F`. This
follow-up narrows the question: §6 contains a candidate generated-call shape,
while its endpoint/path realization and production coverage/admission remain
unspecified. No implementation of those production predicates follows from
retaining more provenance records.

## Conditional source-call derivation

For a source application `f a`, assume the §6 Draft construction is
formalized and its typed path/contract obligation has an endpoint translation.
Let that translation expose a parameter endpoint `P`, and let `I_a` be the
synthesized interface of `a`. The candidate local query is then:

```text
Result(I_a) <: P
```

with its original typed path and contract obligations retained. If this is the
selected translation, resolve it as one ordinary endpoint-dependent
inequality, including local cast or adapter evidence. The candidate query is
independent of an enclosing `F_lit <: F_cb` query: it checks the whole
argument carrier against the parameter endpoint selected by that call
context. Value versus retained-Computation entry then controls how the callee
consumes the accepted carrier; it does not replace or weaken the candidate
inlet query.

If the §6 construction is adopted with this endpoint/path clause, its
syntax-directed derivation carries the local query and matching typed
path/contract evidence. This conditional observation does not establish that
the query is the complete source admission rule, that resolving it alone
admits the source application, or that it covers every well-typed evaluation
context. It does not define the production interpretation allowed by Option 2
or current HIR application nodes, and it composes no successful concrete
comparisons by transitivity.


The approved optional-record counterexample is already covered by the
[endpoint-dispatch characterization](2026-10-05-inequality-endpoint-dispatch-playground.md); it rules out proving a third direct comparison from the two Boolean successes. This audit adds no new finite probe. Whether explicit cast/adapter evidence composes along a callback view remains part of source adequacy, as recorded in the existing
[Pure callback source-path audit](2026-10-03-concrete-compatibility-boundary.md#source-derivation-domain-scope-audit-2026-10-04).

## Production evidence and counterexample search

Current production code retains information useful for a future source-to-
endpoint mapping, but it does not emit the source application clause:

- HIR retains parameter identity and source body occurrences; `LambdaRecipe`
  links the parameter, root, body value/effect and lambda-effect positions.
- F5 `admit_lambda_fact` emits the four-port Function fact. Its pure-effect
  walker checks polarized empty-effect endpoints; it does not determine
  application entry or which complete carrier is admissible.
- The completed `SolvedModule` retains both HIR and `ConstraintStore`, so no
  concrete loss of source/endpoint data or need for a new carrier is shown.
- Current resolved HIR has no callable `Apply` constructor and current F5
  lambda emission admits only integer, own-parameter, or resolved-name body
  shapes. The smallest probe `my call f = f 0` therefore cannot reach
  production Function constraints. This is a production-generation gap, not
  a semantic counterexample.

The bounded source counterexample search found no pair that preserves the
complete typed observation and all retained evidence while changing callback
admissibility. Differences between `id` and `zero` retain different value
dependencies, while differing literal values are deliberately erased by the
approved observation projection.

## Review and verification

The initial independent reviews identified two overstatements, repaired here:

- typed-core §6 is Draft, so its application construction is a source-rule
  candidate, not an established admission rule;
- `Result(I_a) <: P` is conditional on a missing endpoint/path translation,
  and neither inversion nor local-query success alone establishes source
  admission;
- production-to-source challenge correspondence is one sufficient route,
  not a requirement that every Option 2 production member have a constructor
  witness. Exhaustive production admission/satisfaction and containment remain
  the required gate, with independent proof permitted.

The final spec-auditor delta review found no remaining authority or conformance
finding in the repaired text and its synchronized status copies. The bounded
reviews and source inspection do not establish any new semantic rule or
implementation authority.

No tests, builds, measurements, or files outside this record were changed in
the audits. This is an authority/source inspection result, not a proof of
inference soundness, principality, or production containment.

## Required production gate and one sufficient source route

The required gate is an exhaustive, comparison-independent production
definition of `Admit_F(F,h;xi)` and `Sat_F(F,h,O,w;xi)` on the approved
complete-observation basis, followed by proofs of `D_C subseteq D_A` and
`P_A subseteq P_C`, including every Option 2 production-only member and its
typed evidence. Source-generation correspondence from a formalized §6 clause
to the bounded Theorem C reference domain is one sufficient route for source-
generated members; it is not a requirement that all production members have
source-constructor witnesses. An independent containment proof is also
permitted by Option 2. Neither route has yet supplied the exhaustive
production clauses or the full containment theorem. The approved basis does
not itself choose the concrete admission/satisfaction rules. No new user
semantic choice or carrier is established by this audit.
