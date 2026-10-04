# Handler provenance edge projection playground

Date: 2026-10-05
Status: finite characterization only; no semantic, grammar, solver, or implementation authority
Governing candidate: [handler hygiene provenance notation](../design/2026-10-05-handler-hygiene-public-provenance-notation.md)
Review: compiler_referee found no blocking/major issue; two minor scope descriptions were clarified in the script and this record

[`tools/research_handler_provenance_projection.py`](../../tools/research_handler_provenance_projection.py)
checks one-event pairs and exhausts 16 typed-incidence assignments for two
distinct `foo` events, one arriving through input component `e` and one
independent local event. A fixed boundary-order filter removes an event from
the candidate result image only when its own typed-incidence set contains
that boundary. This is an abstract capture filter, not ordinary nested
handler dispatch. The result records ordinary family support separately
from whether an `e`-origin event survives to the result.

The globally smallest family-support collision compares two one-event
histories: an unfiltered `e` contribution and an unfiltered independent local
contribution both yield support `{foo}`, while only the former has the
input-to-result edge. The pairwise two-event search also contains a collision
inside one history shape:

- with no incidence, both events survive, so support is `{foo}` and the `e`
  to result edge is present;
- with the input event incident to the inner boundary, that event is removed
  while the independent event survives, so support is still `{foo}` but the
  edge is absent.

Thus a flat family-support projection cannot determine the provenance edge,
even when the concrete operation instance is the same. Retaining the edge
separates both finite collisions. The checker stipulates that the remaining
support is observed after receiver exit as ordinary output; it does not
simulate the exit or a later handler search.

This evidence is deliberately narrow. The checker supplies incidence sets and
one fixed `foo` contract instead of deriving them from source annotations,
`Rel_C`, `K,D`, `Flow`/`Observe`, receipts, or production Function endpoints.
It assumes one concrete operation instance, and its stipulated post-exit
projection sees only ordinary family support. It therefore does not show that a public `'e?`
scheme preserves distinct type-family assignments or downstream dependencies,
that `Rel_C` projects to the edge, or that the edge semantics is principal.
It does not justify a new carrier or select whether the edge is exact,
may-flow, or a permission. The earlier note's **(B)** recommendation and
open source-to-public projection theorem remain unchanged.

Verification:

```text
python3 tools/research_handler_provenance_projection.py
  pass: one-event provenance collision and 16 ordered boundary-filter incidence assignments
  pass: same-support/different-edge collisions found and separated by edge
git diff --check
  pass
```
