# Current HIR value-skeleton incidence after SCC routing

Date: 2026-10-04
Status: source-generation theorem for a restricted projected structural
package; no implementation or semantic authority
Scope: current error-free binding HIR and F5 value facts after internal uses
and the restricted incoming Int routes
Depends on: Theorem S in
`notes/design/2026-10-04-source-generated-callback-structural-theorems.md`,
the current F5 value-skeleton theorem, and `yu-hir` / `yu-solver` generation
clauses

## Statement

Consider a finite error-free HIR module with unique resolved names whose
definition targets belong to this collected module, and only these binding
and direct-expression forms:

```text
x = integer
x = resolved_module_name
f parameter = integer
f parameter = that_parameter
f parameter = resolved_module_name
direct expression = integer | resolved_module_name
```

There are no nested lambdas in current resolved HIR. Form the actual F5
**value projection** of its collected source facts, internal definition-use
routes, and incoming uses, omitting Function effect children only for this
structural projection. Add the source-checkable restriction that every
cross-SCC resolved `DefinitionUse` targets an alias chain ending at an
integer binding.
Then, after rational equality normalization, every free/free incidence
component satisfies Theorem S: it is either grounded only by closed anchors
or has exactly one open descriptor anchor. Hence, whenever this projected
structural package is satisfiable, it has a simultaneous regular witness.

The restriction is checked by walking the finite HIR dependency graph and
SCC plan, then following each cross-component target through name-binding
aliases to its terminal integer definition. This is independent of the
structural solution and does not assume that a regular solution exists.
It is a sufficient source condition, not a claim that all cross-SCC
instantiations need it.

## Generated constraints and routing

Write `r_d` for a definition root, `v_o` for an occurrence value component,
`p_d` for a lambda parameter, and `F_d` for the existing positive Function
descriptor with its effect children omitted from this projection. The
relevant generated clauses are:

| Source case | Value facts |
|---|---|
| integer binding | `Int <: v_o`, `v_o <: Int`, `v_o <: r_d` |
| resolved-name binding | `v_o <: r_d` |
| identity lambda | `Function(p_d,p_d) <: r_d` |
| integer-body lambda | `Int <: v_o`, `v_o <: Int`, `Function(p_d,v_o) <: r_d` |
| module-name-body lambda | `Function(p_d,v_o) <: r_d` |
| direct integer expression | `Int <: v_o`, `v_o <: Int` |
| direct resolved-name expression | no F5 value bound |
| internal resolved use of target `t` | `r_t <: v_o` |
| incoming use with finalized target predicate `Int` | `Int <: v_o` |

The two directions of the binding alias are distinct generated facts: source
collection connects its occurrence to its parent root, while an internal SCC
route connects the target root to that occurrence. A cross-SCC use is not
generally a raw root edge. F5 finalizes the target scheme and instantiates its
predicate; the present theorem restricts that incoming case to `Int`.

These clauses follow `emit_integer`, `emit_resolved_binding_name`, and
`emit_lambda` in `crates/yu-solver/src/lib.rs`, definition-use collection in
`ConstraintBatch::collect`, internal routing in `route_internal_inner`, and
the `PositiveValueView::Int` branch of `route_incoming_inner`. Direct module
expressions without a binding root do not contribute definition-root value
facts in this collector.

## Incidence proof and separate source-generation theorem

First form the source alias graph on definition roots: every name-binding
root has at most one outgoing target edge; integer and lambda definitions
have no such edge. Each weak component therefore has at most one terminal
producer, or is an alias-only cycle. It cannot join two distinct
integer/lambda producers. The actual post-routing graph retains an edge only
for an internal-SCC use; under the hypothesis, each cross-SCC edge is cut and
replaced by a closed `Int` anchor. A resulting component may therefore end
at an alias root rather than at a producer:

- A component retaining an integer terminal has only closed `Int` anchors.
  A component cut at a cross-SCC alias edge also has only closed `Int`
  anchors; it cannot contain a lambda producer because the cut target's
  alias chain ends at an integer. Multiple cuts add only repeated closed
  `Int` anchors. These components satisfy Theorem S's grounded case.
- A component retaining a lambda terminal has exactly that root's one open
  Function anchor. Lambda parameter occurrences are isolated free
  components; a Function child reference is a constructor edge, not an extra
  free/free incidence edge.
- An alias-only cycle has no descriptor anchor and satisfies the no-anchor
  case. The source restriction prevents an incoming cut from targeting this
  cycle.
- A module-name lambda body occurrence is connected by an internal route to
  the referenced root, or receives the closed `Int` anchor from a restricted
  incoming route. It is a child of its own lambda's Function descriptor, but
  that constructor edge does not merge the lambda root's incidence component
  with the body component.
- An integer lambda body has only its closed `Int` anchors. An own-parameter
  body leaves the parameter component unanchored.

The source-component classification accounts for post-routing alias
fragments, including fragments that terminate at an incoming-Int cut. The
remaining occurrence and parameter components are the body cases listed
above. Together these cases exhaust the source forms and all admitted routes
under the stated restriction. The generated package has no equations, so
rational equality normalization adds no new identifications. Repeated clauses naming the same
descriptor count as one anchor. Rigid-name permissions are vacuous.
Theorem S therefore supplies the stated regular witness.

This is also the source-generation theorem: the finite HIR walk enumerates
exactly the listed expression forms and name resolutions; the collector emits
the tabled facts; SCC routing emits either the internal root-to-use bound or,
under the stated incoming restriction, a closed `Int` lower bound. The
incidence proof is separate from the regular-witness theorem and checks the
generator's output without solving it. The proof includes forward references,
alias chains ending in integers, alias-only cycles, and mutually recursive
lambdas; these do not create multiple anchors in one free/free component.

The broader theorem-scoped package in which every resolved use is replaced
by a monomorphic root edge `r_t <: v_o` satisfies the same incidence
argument for this entire HIR grammar. That package is not the production
cross-SCC scheme-instantiation behavior and is not substituted for it here.

## Boundary

For example, `my k x = 42; my g = k` is outside the incoming-Int restriction,
but is not a counterexample to Theorem S incidence: F5 instantiates a closed
`Function(Top,Int)` descriptor at `g`, so that component has a closed anchor;
`k` retains its separate open Function anchor. The second source-generation
case therefore does not merge those components.

Arbitrary structured incoming schemes remain open. Scheme instantiation may
expand unions or recursive bounds into several descriptor anchors, and
Function children can contain `Top`/`Bottom`, which Theorem S's stated pure
structural package does not automatically admit. A separate theorem must
show that F5 generalization, structured instantiation, and extrema
normalization preserve a permitted incidence package, or certify the
resulting finite package with the existing multi-anchor selector. No current
source counterexample to regular completion is established here.

This result proves neither equivalence with the coupled four-port F5 package
nor full F5 satisfiability, effect-port denotation, callback adequacy,
scheme principality, or successor inference correctness. It adds no carrier,
source rule, or rejection policy. Independent compiler-referee and
spec-auditor reviews confirmed the component classification and source
mapping; the incoming-Int cut case was clarified after review. No code or
tests changed or ran.
