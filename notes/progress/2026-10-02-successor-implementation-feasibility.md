# Successor implementation feasibility checkpoint

Date: 2026-10-02
Branch: `research/simple-sub-intrusion`
Status: read-only architecture audit; no implementation authority

## Result

The selected nested-capture preservation clause is not currently implementable
as an end-to-end Yulang3 feature without substantial front-end and effect-model
work. The obstacle is not the ability to store another solver relation: the
current compiler surface does not represent the source transitions that the
proof obligation quantifies over.

Repository evidence:

- `crates/yu-hir/src/lib.rs::HirExpr` retains syntax-associated operator
  applications as `Apply`, so the parser/association layer has a useful
  application-shape substrate. The later source-resolved
  `crates/yu-hir/src/module.rs::ResolvedExpr` currently has only `Lambda`,
  `Integer`, `Name`, and `Error`; it has no resolved call/application, typed
  thunk/force, operation request, handler, or resumption nodes. `HirExpr::Apply`
  is syntax association data, not a resolved evaluation or inference step.
- `crates/yu-solver/src/lib.rs::Collector::emit_lambda` handles a narrow set
  of lambda bodies (parameter name, integer, resolved name); its other shapes
  return without a lambda recipe. There is no call or handler transition to
  attach the selected `Visible` preservation law to.
- `crates/yu-types/src/lib.rs` has polarized Function nodes with argument and
  result effect endpoints, but closed `PositiveEffectView` and
  `NegativeEffectView` expose only `Bottom` and `Empty`. This is insufficient
  to publish the successor's nonempty typed request rows and symbolic family
  constraints.
- `crates/yu-solver/src/lib.rs` already has a bounded substrate—polarized
  terms, value/effect variables, levels, directed bounds, extrusion, typed
  pairs, and F5 generalization/instantiation. This is useful characterization
  and possible migration substrate; it does not implement the successor
  `Rel_C`, callback origins, handler search, or `K,D` symbolic lifecycle.
- The current closed-scheme substitution in
  `crates/yu-solver/src/f5c_binder_substitution.rs` traverses Function value
  argument/result edges, but reconstructs effect fields as `Empty` / `Bottom`.
  The current representation therefore cannot serve as a direct implementation
  of uniform typed-family/effect transport; it would need a new carrier or a
  reviewed replacement of the F5 path, not a thin reuse of its binder walker.

## Feasibility classification

| Slice | Current feasibility | Evidence / boundary |
| --- | --- | --- |
| Pure finite SCC parent-map prototype | Plausible as an isolated research model after its theorem fixes the parent ports and observations | Existing polarized graph and SCC machinery provide useful input/output handles, but the current F5 publication contract is explicitly not the successor target. |
| Symbolic typed-family transport through solving and SCC lifecycle | Not ready to implement | The successor obligation identity, denotation, solving/residualization transitions, and parent quotient remain candidate mathematics; inventing storage now could freeze a representation before the proof. |
| Nested callback capture preservation in compiler | Not presently expressible end to end | HIR and source collection lack calls, handlers, force, and resume, while closed effect schemes cannot retain nonempty typed rows. |
| Full successor replacement | Large cross-layer change | Requires source syntax/HIR/evaluation interfaces, effect denotation and principal finite presentation, solver/lifecycle transport, then runtime/compiler integration and method/role/impl gate. |

The safe implementation conclusion is therefore **defer compiler changes for
the current preservation proof gate**. The existing graph substrate offers
some useful ownership/arena patterns, but its current scheme substitution
erases precisely the effect payloads that the successor must transport.
Continue alternating theory work with read-only code feasibility checks. Once
a narrow mathematical slice is
reviewed and implementation authority exists, prefer an isolated Rust
executable characterization over a Python side model, then assess whether it
maps to the existing solver substrate before changing production paths. This
checkpoint does not authorize that model or any compiler edit.

## Next gate

Return to the source call/handler relation and prove the composition premises
for callee/argument evaluation, both adaptations, callback origin, force,
ordered search, and raw resume. After each closed semantic slice, inspect the
corresponding HIR/solver/type representation and record whether it is directly
implementable, needs a bounded prototype, or requires a larger architecture
change. Method selection, roles, and implementation resolution remain a later
mandatory gate.

## Alternating proof / feasibility check: event identity

The callback-origin proof now distinguishes four coordinates: a static source
site template, an individual dynamic request event, the source computation or
callback/thunk value lineage, and an activation identity. Repeated execution
may create a new event from the same template and lineage; symbolic type
transport changes typed endpoints and `K,D`, not runtime event or activation
IDs. A delta review of this distinction found no issue. This closes only the
identity bookkeeping question, not the conditional source `Force` /
`B_{S,T}` preservation premise or the full soundness and principality proof.

The corresponding code check found no existing representation for source
origins, callback/thunk lineage, or these activation coordinates. Syntax HIR
does retain associated operator applications, but the resolved HIR and solver
collection path have no call/handler/force semantics to attach lineage to; the
current closed effect views also remain singleton `Bottom` / `Empty`. So the identity
distinction can be described in the proposed relational interface, but there
is no present compiler path where it can be implemented or exercised. This
reinforces the current decision to alternate proof slices with read-only
feasibility checks and defer production changes until the semantic carrier is
settled and implementation authority is granted.

No source code was changed. No tests or builds were run.
