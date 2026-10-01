# Mixed-ownership fixture audit for SCC member views

Date: 2026-10-01
Branch: `research/simple-sub-intrusion`
Reference: frozen Yulang2 Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Status: fixture inventory; no successor semantics or proof conclusion

This audit follows the conditional joint member/use map criterion. It asks
whether existing source witnesses establish one exact saved `TypeVar` that is
local in one member's finalized scheme and preserved free in another member's
scheme. The current artifacts do not establish that same-SCC case.

## Closest observed witnesses

The exact raw-identity mixed-ownership observation is the nested local diamond
in `notes/progress/2026-09-29-intrusion-oracle-ledger.md:36`: `outer` quantifies
its parameter, while nested `inner` leaves the same `TypeVar` free as a
captured outer identity. This demonstrates why ownership cannot be inferred
from the raw ID alone. The two bindings belong to nested components, however,
not two member projections of one SCC. The attempted local mutual-recursion
variant in the ledger reports `UnresolvedName`, so that source spelling does
not provide the missing case.

The guarded two-member source witness in
`notes/progress/2026-09-30-intrusion-bounded-negative-counterexample.md:595-638`
places `helper` and `g` in one `QuantifyComponent`, with distinct incoming
uses. The record states that both finalized schemes have the same three-Q
vector and distinct recursive-bound binders. It does not record complete
finalized Q/R sets or all type-variable occurrences in both predicates and
recursive-bound sides, so it cannot establish either the presence or absence
of mixed Q/R-versus-free ownership.

`analysis/tests/case_03.rs::computed_fetch_def_does_not_quantify_binding_level_root`
compares `FetchValue` and `FetchComputation` in separate sessions. It proves
their boundary distinction for one identity-function shape, but it does not
share one source ID across two member schemes. A naive two-member cycle with a
computed-fetch target is reported as `ComputedFetchCycle` by
`scc/graph.rs:658-675` and `scc.rs:399-407`; the error path is exercised in
`lowering/tests/case_07.rs:5908-5960`. That rules out this obvious accepted
source construction, not all root-projection or other-source constructions.
The diagnostic is routed to `BodyLowering.errors` and nonempty errors fail the
normal runtime-ready build gate (`analysis/session/selection.rs:1121-1136`,
`lowering/body/mod.rs:1664-1691`, and `yulang/src/source/mod.rs:1973-1976,
2293-2299`). The cycle may still proceed through recovery/publication, but it
does not supply a normally accepted program for the compatibility target.

## Current inference and remaining evidence

The source mechanism does permit a different boundary per definition
(`analysis/session/generalize.rs:767-774`, `typing.rs:89-103`), processes member
roots sequentially (`analysis/session/instantiate.rs:14-39`), and can prune
quantifiers during finalization (`generalize/mod.rs:837-864`). These facts make
the mixed case a real question, but they do not demonstrate it. Root-epoch
metrics also do not reconstruct every intermediate compact view, as recorded
in `2026-10-01-intrusion-oracle-root-epochs-and-use-context.md`.

There is a useful conditional exclusion for Q-versus-free ownership. For a
variable `v` that occurs in both roots' compact-plus-role views where their
quantifiers are selected, if both roots use the same boundary and
`level_of(v)` is unchanged across those epochs, the strict-level predicate
classifies `v` identically. Finalization's dead-quantifier pruning only
removes binders absent from compact root and roles
(`generalize/core/prune.rs:155-163`); it cannot turn a retained occurrence
into an unquantified free occurrence while keeping it as the same root
variable. Therefore an accepted-source Q/free split needs a premise outside
that uniform case: differing boundaries, level lowering between member
epochs, or a later root/scheme rewrite that introduces the identity after its
quantifier set was chosen. This is a conditional consequence of
`quantified_vars_in_root_and_roles` and the finalizer, not proof that any of
those mechanisms occurs in an accepted SCC.

The Q argument says nothing about R ownership. Recursive-bound variables are
collected by root-local polarized DFS and pruned by root reachability
(`compact/collect/mod.rs:190-207, 761-784`,
`generalize/core/prune.rs:90-123`); one member can in principle retain an R
binder while another view contains that identity through a different path.
The current guarded source record names distinct R binders but omits the
cross-root occurrence inventory needed to decide this case.

The next useful source evidence must come from one accepted same-SCC
construction or a complete saved graph view. It must align, for both member
roots, the same pre-finalization machine identity with:

1. published `scheme.quantifiers` and finalized recursive-bound variables;
2. occurrences in the finalized predicate, roles, and both recursive-bound
   sides; and
3. the per-use clone mapping or the source elaboration rule that determines
   whether that occurrence remains shared.

If no source program can express such a witness, the proof must say so and
derive the member-view ownership classes from the source-defined graph
construction instead. Focus the next source trace on the guarded SCC's
per-root compact support, levels at Q selection, ancestor substitutions,
final Q/R sets, and free occurrences; separate any epoch lowering or
post-quantifier rewrite from the recursive-bound reachability case. The
existing two-view example in the candidate proves only renaming algebra after
ownership classes are supplied. It does not close source-step adequacy, all
member-root observations, effects, principality, or final acceptance
equivalence. No compiler code or test file was changed and no test was run for
this audit.
