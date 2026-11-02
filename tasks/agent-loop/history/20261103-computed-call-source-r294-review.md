# Computed Call source supplier R294: independent review

`/root/r294_independent_lean` and `/root/r294_parent_review` independently
reviewed the frozen module and handoff. Module SHA-256
`4056741b5c7506389f2e04c91a8b18f8527891ba9dca3a1888bf10f20d8797a4`;
handoff SHA-256
`06e25317b9d42428be296a3e5c3537b0b445f7c406995a3d551f847afc956547`.
All 22 dependency pins matched. The Lean reviewer independently ran the pinned
Lean 4.35.0 checker in an isolated project; all five new theorems and the
selected R293/R159 theorems passed. Full types and axiom lists are in the
handoff: the five R294 results and R159 use `propext`, `Classical.choice`,
`Quot.sound`; R293 `app_result_pair` uses `propext`, `Quot.sound`.

For the fixed unannotated nested App `(f x) y`, the actual `sourceOwners` walk
has no event owners and its `sourceRecord` is `none` for all represented
assignments and raw records; the separate static Call registry still contains
the outer Call. Context and names remain arbitrary. This rules out constructing
its EI phase record solely by reading that particular event-binder registry.
It does not show that other registries cannot supply EI, that runtime events are
absent, or that an untyped source is a semantic counterexample. GR1 registers a
logical ViewLogic description and does not require this `sourceRecord`.

Actual EI phase interpretation, CalRet-dependent argument/challenge telescopes,
original arm inventory and dependent result fields remain to be constructed.
Original image-to-synthesis checking and logical admission are independent.
Neither R159 nor source/native correspondence is closed; parent delta is zero.
Both reviewers stopped without repository or shared-cache writes.
