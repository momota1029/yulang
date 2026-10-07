# Shadow Apply/formal to current scheme origin — round 16

Baseline: latest pushed `origin/research/simple-sub-intrusion` at
`7bf7083419f677eacaf1b76525ce4c06bc2da908`.

The focused experimental HIR fixture
`my apply f = f input; my input = 1; pub alias = apply` follows these exact
current identities:

```text
HIR parameter f
  → PendingApplicationOccurrence.callee resolution to that HirParameterId
  → captured solver startup row for f
  → target definition's current finalized scheme
  → incoming alias use's current fresh capture
  → receiving alias scheme
```

The HIR/core skeleton crosswalk cannot register the formal or the direct call
for this multi-item module. The solver row and HIR parameter still join through
the row's exact retained resolution; source positions identify the exact call
and formal occurrences, but do not manufacture the missing core registration.
The captured startup row has no match in the target scheme's current
generalization-origin map. Therefore no target binder is selected, and no
parameter-to-fresh-row-to-receiving-origin correspondence is asserted. Empty
fresh/origin inventories do not establish absence under successor semantics.

The pending state remains `ApplicationTypingRuleUnresolved`; successor
generalization, current-to-successor Q/R correspondence, and shared-contract
transport remain unresolved. `pub` is metadata only. Current production HIR
refuses ordinary Apply here; the fixture uses the explicitly experimental
shadow-application lowering and does not claim source acceptance or parity with
old production inference. Ordinary and capture solver diagnostics and
occurrence projections agree. Full `ProductionCounters` equality was not
established; an attempted assertion differed in observer query-probe counts,
so the test makes no cross-run counter-parity claim. It does verify that
reading the captured identities leaves the captured solve's counters
unchanged.

Independent compiler-referee review and delta review passed the narrowed test
claim. The full `shadow_receiving_root_scheme_crosswalk` target passed (4 tests)
with `shadow-f5` and `shadow-scc-observer`. No production path or DAG status
changed.
