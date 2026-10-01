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
uses. A focused trace against the frozen Oracle now records its Q selection,
ancestor state, and finalized binder sets (below). In this fixture the two
cross-recursive variables are both Q binders in both member schemes; it does
not exhibit a Q/free or R/free split.

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

A source review narrows these possibilities but does not remove them. Boundary
lookup is per definition (`typing.rs:96-103`,
`analysis/session/generalize.rs:767-776`); the path contains no
component-wide boundary normalization. Ordinary mixed-fetch internal uses
that target a computed member are diagnosed as `ComputedFetchCycle`
(`scc/graph.rs:658-676`), so this familiar source shape is not an accepted
witness. However, payload-free `DependencyAdded` edges can participate in an
SCC and are produced for role requirements and pending role candidates
(`scc/graph.rs:147-156`, `analysis/session/lifecycle.rs:359-369`,
`analysis/session/selection.rs:43-71`). Thus a mixed-fetch SCC without the
computed-use diagnostic is source-permitted at the scheduler level; no
accepted source fixture with a shared identity across such member views has
been found. This does not start the later method/role semantics gate.

As a negative control, the existing accepted role-method/helper recursion at
`lowering/tests/case_07.rs::role_impl_method_lifecycle_slice4c_t4_receiver_and_ordinary_binding_recurse_in_one_component`
was run with the temporary trace enabled. Its two jointly quantified roots
both selected `TypeLevel(0)`, with unchanged constraint epoch `(37, 37)`, no
Q binders, and no recursive binders. The focused test passed. This confirms
that this existing role cycle supplies no differing-boundary or mixed-owner
witness; it says nothing about other dependency-only SCCs or cross-epoch
lowering. The command was
`YULANG_INTRUSION_OWNER_TRACE=1 CARGO_TARGET_DIR=/tmp/yulang-intrusion-scc-owned-target cargo test --offline --jobs=1 -p infer role_impl_method_lifecycle_slice4c_t4_receiver_and_ordinary_binding_recurse_in_one_component -- --nocapture --test-threads=1`.

Likewise, levels are mutable shared machine state and only move downward
(`constraints/mod.rs:458-467`). Bound insertion can extrude endpoints
(`constraints/machine/bounds.rs:630-645, 815-830, 4701-4727`), while the first
member's generalization prepasses may add constraints before the next member
is selected (`analysis/session/generalize.rs:103-125, 168-200, 327-336,
478-511, 536-543`; `analysis/session/instantiate.rs:14-39`). Each Q selection
reads the then-current level (`generalize/mod.rs:900-915`). Cross-epoch
lowering is therefore possible in the mechanism, but still lacks an accepted
source witness changing a shared identity's Q classification.

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

The Q argument says nothing general about R ownership. Recursive-bound variables are
collected by root-local polarized DFS and pruned by root reachability
(`compact/collect/mod.rs:190-207, 761-784`,
`generalize/core/prune.rs:90-123`); one member can in principle retain an R
binder while another view contains that identity through a different path.
The focused guarded-source trace below shows the two cross-recursive IDs are
Q binders in both views, but does not establish a general exclusion for R/free
ownership in other SCCs.

## Focused trace of the guarded two-member SCC

The frozen Oracle was built in a detached scratch worktree at the reference
revision. Temporary instrumentation in `instantiate.rs` and one focused test
captured the existing accepted source fixture; neither was added to this
branch. The trace is `/tmp/yulang-intrusion-owner-trace.log` and the focused
command passed once:

```text
YULANG_INTRUSION_OWNER_TRACE=1 CARGO_TARGET_DIR=/tmp/yulang-intrusion-scc-owned-target cargo test --offline --jobs=1 -p infer scratch_intrusion_same_scc_member_ownership_trace -- --nocapture --test-threads=1
```

| Member root | Boundary | Constraint epochs | Q selected and published | R published | Ancestors |
| --- | --- | --- | --- | --- | --- |
| `helper`, `TypeVar(9)` | `TypeLevel(0)` | 298 → 299 | `[11, 97, 98]` | `[97]` | none |
| `g`, `TypeVar(39)` | `TypeLevel(0)` | 299 → 300 | `[11, 97, 98]` | `[98]` | none |

At both Q-selection points, variables 97 and 98 had level 1. Thus the root
epoch advanced, but this trace shows neither a level change nor a Q ownership
change. The helper scheme's recursive binder is 97 and its lower recursive
payload reaches 98; the g scheme owns 98 and its lower payload reaches 97.
Both IDs are Q binders in both schemes, so these cross-recursive occurrences
are Q/Q. The captured incoming clone maps use pairwise-disjoint target triples
for the Q vector, consistent with independent freshening per use.

This closes the inventory gap for this fixture only. It does not prove that
every accepted source SCC preserves uniform Q ownership, or settle whether
another fixture can expose root-local R/free ownership, boundary variation,
level lowering, or a post-selection graph rewrite.

The next useful source evidence must come from one accepted same-SCC
construction or a complete saved graph view. The narrow probe is a
diagnostic-free dependency-cycle with mixed fetch classes and one shared deep
variable, recording its level and both Q sets around a constraint-producing
first-member prepass. It must align, for both member
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
equivalence. The scratch Oracle worktree and instrumentation are temporary
characterization only; no compiler code or test file was changed on this
branch.
