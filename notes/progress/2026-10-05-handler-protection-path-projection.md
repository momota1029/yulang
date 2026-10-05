# Handler-protection release over typed-path evidence

Date: 2026-10-05
Status: finite characterization; no semantic, grammar, solver, or implementation authority
Review: compiler_referee; two major model defects repaired and delta review closed clean
Probe: [`research_handler_protection_path_projection.py`](../../tools/research_handler_protection_path_projection.py)

This follow-up tests one possible query-time projection of the corrected
`'e?` meaning over the existing evidence vocabulary. The meaning itself is
the local protection-only change: for an already attributed contribution
leaving the marked slot, stop protecting it from handlers while preserving its
provenance and all other evidence. The probe does not define that operation.
In particular, the hypothesis that a typed route must cross a marked slot is
only one candidate for locating where the operation applies. It keeps the
following distinction explicit:

- Raw `Path` is derived from supplied boundary profiles, typed `Flow`,
  `Observe`, and matching `Receive` evidence. Release marks do not change it.
- `Inc_C` filters that raw path relation by active handler, candidate owner,
  and profile receiver, matching the typed-boundary candidate definitions.
- One candidate post-marker protection query asks whether an active
  incidence has a typed route that bypasses the marked slot. Any independent
  unmarked path keeps its protection under this candidate. `Visible` then
  applies ordinary active owner, family coverage, and grant conditions. This
  path-crossing rule is not selected semantics and could be replaced if the
  source lifetime rules identify the release point differently.

This is a computed query over supplied source evidence, not a new stored ledger
or a source rule. The small finite model covers 17 cases: distinct same-family
local contributions, two independent paths for one event, a returned latent
result observation, a distinct resumed event under the same source/K,D labels,
receiver expiry with a separate active outer-handler owner, candidate-owner
expiry, and cyclic `Flow` graphs both before and after the exposure target.
Family-wide release, sticky protection, and provenance/Path erasure mutants
are rejected. Product-state reachability tracks whether a typed path crossed
the exact marker without making raw path or incidence depend on that marker.

The graph-query implementation also has a finite exactness check independent
of those hand-selected cases. Its state space is `(typed-position,
crossed-marker)` with at most `2|V|` states. Worklist reachability is sound by
construction of each transition from one supplied `Flow` edge; it is complete
because every finite marked/unmarked walk induces a path in this product graph.
Any reachable state has a simple product-state witness of at most
`2|V|-1` edges, so bounded raw-walk enumeration to that length is a complete
oracle even when the input graph is cyclic. Differential comparison checked
all 37,124 graph/marker/source/target configurations across 530 directed
`Flow` graph structures through three typed positions. This validates the query against the
supplied graph only; it exercises `graph_release_states`, not the full
`release_route_states` path-filter layer. It does not establish that route
crossing is the meaning of `'e?` or identify the source-selected release
lifetime.

The result suggests that a protection-only query projection could reuse
`Rel_C`-shaped `Profile`/`Flow`/`Observe`/`Receive`/`Path`/`Inc_C` evidence
without rewriting event provenance or adding a persistent carrier, provided
the source derivation supplies component attribution and the marked slot is
recoverable from its typed path. This conditional evidence is only a
characterization of that projection hypothesis, not evidence that path
crossing defines release. It does **not** prove that Yulang source generation
supplies those premises, that the model's per-path filter is the intended
release point for every callback/lifetime case, or that production handler
dispatch is adequate. The open source-to-public gate still includes
annotation-to-slot attribution, overlapping/nested semantics, actual
continuation transitions, public scheme ordering, and syntax ownership.

Verification:

```text
PYTHONDONTWRITEBYTECODE=1 python3 tools/research_handler_protection_path_projection.py
  pass: 17 bounded evidence cases; three mutants rejected
  pass: 37,124 graph/marker/source/target configurations across 530 Flow graphs agree with bounded raw walks
git diff --check
  pass
```
