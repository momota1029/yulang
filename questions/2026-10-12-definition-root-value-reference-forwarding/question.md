# Definition-root Value-reference ownership

Question ID: 2026-10-12-definition-root-value-reference-forwarding
Question revision: 1
Predecessor/history: `2026-10-12-apply-result-value-reference-owner`, revision 1
Original worktree: /home/momota1029/rust/yulang
Branch: research/simple-sub-intrusion
Relevant source revision(s): `c4224d749` (research checkpoint); working proof handoff has a reviewed approval-boundary correction
Task/thread locator: current working conversation; external locator unavailable
Governing source/section: `notes/design/2026-10-10-parent-copy-scc-intrusion.md`, “Value-reference SCC clarification”, “Apply-result source-fragment ownership”, and “Retained boundary”

## Requested scoped decision

The accepted source-owner abstraction for

```yulang
my odd n = { my even n = odd(n); even(n) }
```
has `even → odd` from the inner initializer and `odd → even` from the outer
final expression. The approved Apply decision separately gives each Apply
result row edges to its resolved Names. The native constructor audit shows the
module definition root `O`, outer Lambda row `L`, block row `H`, local `even`
root `E`, and Apply results `R,S` are separately allocated; typing links such
as `L <: O` do not themselves create Value-reference edges.

Choose how definition publication contributes to the **Value-reference** graph:

1. **Definition-root ownership:** the published definition root owns the
   resolved Name references in its source-owned initializer/body, with nested
   declaration initializers owned by those declarations. For this example,
   `O → E` and `E → O`; the independently approved Apply rule also retains
   `R → O` and `S → E`. These are reference incidences, not row equalities or
   edges inferred from typing constraints.
2. **Expression-row ownership:** Apply and other expression rows own only the
   references assigned directly by their constructors. Definition publication
   forwards those incidences only where an explicit Value-construction rule
   says it does. Under the inspected constructors alone, `L <: O` does not
   supply `O → E`, so the source-owner cycle is not yet established as a
   native `O/E` SCC. A further explicit forwarding rule would be needed if
   binder-level cycles are intended to qualify intrusion.

The reviewed comparison note records both completions as conditional models;
original Simple-sub itself defines a type/bound graph and does not select this
Yulang Value-reference ownership rule. The recommended choice is option 1
because it preserves the already accepted source-owner reference meaning on
the actual binder roots while keeping Apply-result incidence separate.

This question selects only definition-root ownership at publication. It does
not resolve nested Apply fragment membership, prove extrusion/fresh-use
transport, qualify any extrusion pair, or establish intrusion equality
soundness/principality, complete Call, effects, public cutover, or F5 replacement.
