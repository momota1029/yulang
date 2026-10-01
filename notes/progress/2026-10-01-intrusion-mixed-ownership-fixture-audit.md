# Mixed-ownership fixture audit for SCC member views

Date: 2026-10-01
Branch: `research/simple-sub-intrusion`
Reference: frozen Yulang2 Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Status: fixture inventory; no successor semantics or proof conclusion

This audit follows the conditional joint member/use map criterion. It asks
whether source witnesses establish one exact saved `TypeVar` that is local in
one member's finalized scheme and preserved free in another member's scheme.
No accepted source fixture establishes this. A synthetic same-SCC
`AnalysisSession` characterization below demonstrates the split at the Oracle
machine level, without establishing source construction or final program
acceptance.

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

## Synthetic same-SCC ownership witness

A disposable test in the detached Oracle worktree manually drove the
`AnalysisSession` lifecycle, without source lowering. It registered two roots
with the same depth-1 variable in both predicates, gave one member
`FetchValue` and the other `FetchComputation`, then queued a pair of
payload-free `DependencyAdded` edges before finishing either definition. It
asserted a component merge, exactly one joint `QuantifyComponent`, no analysis
diagnostics, and retained occurrences of the shared variable in both
generalized compact roots. The finalization trace independently shows the
same occurrences in both published predicates.

The focused trace reports:

| Member | Boundary | Constraint epoch at Q selection | Q | Shared variable occurrences |
| --- | --- | --- | --- | --- |
| value-fetch root 700 | `TypeLevel(0)` | `(2, 2)` | `[702]` | argument and return |
| computation-fetch root 701 | `TypeLevel(1)` | `(2, 2)` | `[]` | argument and return |

The shared variable 702 remains at `TypeLevel(1)`. This is a concrete
same-component Q/free split in the Oracle's session machinery, caused solely
by per-definition fetch boundaries; it does not depend on cross-epoch level
lowering, post-selection rewriting, or recursive-bound ownership. Under the
ordinary use-map rule characterized in
`2026-10-01-intrusion-oracle-root-use-ownership-audit.md`, a use of root 700
maps 702 freshly, while root 701 preserves 702. This is evidence that an
SCC-wide unpartitioned identity set cannot model all member schemes. It does
not show that source
lowering can produce this exact dependency-only mixed-fetch component, that
the resulting module is accepted, or that Oracle final specialization exhibits
a user-visible difference.

The disposable focused command passed once:

```text
YULANG_INTRUSION_OWNER_TRACE=1 CARGO_TARGET_DIR=/tmp/yulang-intrusion-scc-owned-target cargo test --offline --jobs=1 -p infer scratch_intrusion_dependency_cycle_mixed_fetch_shared_identity -- --nocapture --test-threads=1
```

No Oracle source or test change was committed, and the Yulang3 branch was not
modified by the probe.

## Exclusion-theorem counterexample and source probe

An independent compiler-referee audit rejects the proposed structural
exclusion that every `DependencyAdded` target is a value-fetch member. The
selection path adds a payload-free dependency to every unready role-impl
member. A receiverless, zero-parameter member returns its body computation;
`our make = helper 0` can therefore be `FetchComputation`. The computed-cycle
check examines only internal use edges with a payload whose target is
computed. Consequently this graph shape is admitted by the SCC machine:

```text
computed make --UseResolved--> value helper --DependencyAdded--> make
```

The graph argument disproves the proposed fetch-uniformity invariant but is
not itself a source program or compiler bug report. A source candidate was
probed in the detached Oracle worktree: a scalar role member `make` calls a
typed top-level helper, while that helper selects a role method on `int`.
The focused lowering test reported no errors, but its SCC trace contained
separate quantifications, a `make -> helper` component edge, and no
`helper -> make` dependency or mixed SCC. This probe therefore does not
establish source reachability or final runtime-ready acceptance. The synthetic
same-SCC Q/free witness remains machine-level evidence only.

The next source investigation must explain why a concrete role demand in the
helper does not add the candidate edge in this ordering, then either produce a
source trace that reaches the mixed-fetch dependency cycle and passes the
normal final-acceptance gate, or prove a narrower source-level restriction.
The general graph exclusion is withdrawn. No changes were made to the frozen
Oracle checkout or to compiler source on this branch.

A follow-up trace instrumented the four candidate-edge gates for this source
candidate. The `Pair` impl candidate was visible (`Some(DefId(3))`), but the
only `Pair` constraints present during dependency scans belonged to the role
method declarations and failed `role_constraint_could_resolve`; both scans for
the top-level helper had an empty role list. The events later show an
`InstantiateUse` from the helper to the role's `read` signature, but no
`DependencyAdded` from helper to `make`. Thus this candidate fails at the
earliest gate: it does not create an owner-local role constraint for the
helper before its dependency scan. The focused scratch test still reports no
lowering errors and separate quantifications; it did not run the full
runtime-ready acceptance pipeline. This narrows the next probe to a source
form that inserts a concrete role predicate on a value-fetch owner before
`DefFinished`/`MethodDependencyResolved`, while that owner's use edge reaches
an unready computed member. The trace instrumentation and fixture remain in
the detached scratch checkout only.

## Accepted source mixed-fetch dependency SCC

A second source construction reaches the dependency-only mixed-fetch shape.
The role has a receiverless `make` member and a receiver method `probe`; the
generic `demand` function retains a `Pair` predicate through `x.probe`. Inside
the `int: Pair` implementation, `owner` is a local lambda that instantiates
`demand(1)` and selects `1.probe`, while the receiverless computed `make`
calls `owner()`:

```text
role Pair 'subject:
  our make: int
  our x.probe: int
my demand(x: 'a): int =
  where 'a: Pair
  x.probe
impl int: Pair:
  my owner = \() ->
    demand(1)
    1.probe
  our make = owner()
  our x.probe = 1
pub result = 0
```

The owner scan first sees no roles. Later the instantiated concrete `Pair`
constraint is present, passes `role_constraint_could_resolve`, and sees the
candidate implementation with `make` still unready. The trace records
`unready=[make]`; the owner-to-make dependency then closes the SCC with the
ordinary make-to-owner use edge. Exactly one joint `QuantifyComponent`
contains owner and make, with no lowering diagnostics. The focused final
acceptance probe calls `specialize_mono_from_sources`, which passes the
runtime-ready gate and monomorphic specialization with no errors.

The boundary trace confirms the intended mixed fetch: owner selects
`TypeLevel(0)` and receiverless make selects `TypeLevel(1)`. Both roots happen
to have empty Q/R sets and concrete predicates. This is source reachability
and final-acceptance evidence for a mixed-fetch dependency SCC; it is not a
source witness for the earlier shared-variable Q/free split, nor a runtime
execution result. Both fixtures and all instrumentation remain in the
detached Oracle worktree; no compiler source or test file on this branch was
changed. The focused commands were:

```text
YULANG_INTRUSION_ROLE_DEP_TRACE=1 CARGO_TARGET_DIR=/tmp/yulang-intrusion-scc-owned-target cargo test --offline --jobs=1 -p infer scratch_intrusion_source_local_value_computed_member_dependency_cycle -- --nocapture --test-threads=1
YULANG_INTRUSION_ROLE_DEP_TRACE=1 CARGO_TARGET_DIR=/tmp/yulang-intrusion-scc-owned-target cargo test --offline --jobs=1 -p yulang scratch_intrusion_mixed_fetch_dependency_cycle_runtime_acceptance -- --nocapture --test-threads=1
```

The remaining ownership question is whether an accepted source can make the
same pre-finalization TypeVar appear in both roots' retained views while one
root quantifies it and the other leaves it free. This accepted mixed-fetch
fixture does not answer that question. Cross-epoch lowering and root-local
R/free ownership remain separate.

## Accepted source Q/free ownership split

The same mixed-fetch dependency construction also admits a retained shared
TypeVar split. Change the role member signature to `'b -> 'b`; make the
value-fetch owner return an identity function, and let the receiverless
computed `make` call the owner:

```text
role Pair 'subject:
  our make: 'b -> 'b
  our x.probe: int
my demand(x: 'a): int =
  where 'a: Pair
  x.probe
impl int: Pair:
  my owner = \() ->
    demand(1)
    1.probe
    \x -> x
  our make = owner()
  our x.probe = 1
pub result = 0
```

In one `AnalysisSession`, the source trace records owner DefId 5 and make
DefId 6 in exactly one joint `QuantifyComponent`. The owner boundary is
`TypeLevel(0)` and its Q vector is `[TypeVar(38)]`; make's boundary is
`TypeLevel(1)` and its Q vector is empty. The trace shows the same TypeVar 38
as both argument and result in each finalized predicate. Direct assertions in
the focused scratch characterization check the common SCC, the owner's single
Q binder, the empty make Q vector, and an exact `Var('38)` node in both raw
schemes. The dependency scan for owner sees concrete `Pair` and
`unready=[make]`. No lowering diagnostics occur.

The identical source is accepted by the focused Yulang path through
`specialize_mono_from_sources`: runtime readiness and monomorphic
specialization both succeed with no errors. This is now a source-level,
final-compilation witness that the same shared TypeVar can be Q for a
value-fetch SCC member and free for a computed-fetch member. Therefore the
successor cannot classify variables once per SCC and infer ownership from
that shared classification; it needs member-view ownership while retaining
the shared source identity. The result is one counterexample fixture, not a
principality proof or a complete Oracle capability comparison. Runtime
execution remains untested. The scratch fixture and all instrumentation are
detached-only; neither compiler source nor test files on this branch changed.

Focused commands:

```text
YULANG_INTRUSION_OWNER_TRACE=1 YULANG_INTRUSION_ROLE_DEP_TRACE=1 CARGO_TARGET_DIR=/tmp/yulang-intrusion-scc-owned-target cargo test --offline --jobs=1 -p infer scratch_intrusion_source_mixed_fetch_shared_polymorphic_result -- --nocapture --test-threads=1
YULANG_INTRUSION_ROLE_DEP_TRACE=1 CARGO_TARGET_DIR=/tmp/yulang-intrusion-scc-owned-target cargo test --offline --jobs=1 -p yulang scratch_intrusion_mixed_fetch_shared_q_free_runtime_acceptance -- --nocapture --test-threads=1
```

## Rejected recursive-result variant

One follow-up replaced the owner's identity result with an argument
self-application (x applied to itself) to look for a recursive-binder
ownership split. Inference finalized owner with
`Q=[38,41,42]`, `R=[41]`; make had `Q=[]`, `R=[41]`. The shared recursive
variable was therefore R/R. This trace does not establish the ownership of
TypeVar 38 in make's finalized predicate.
The scratch lowerer reported no diagnostics, but the final monomorphic
specializer rejected this variant with `UnsatisfiedSubtype` (`unit` against a
function). It is not a final-accepted source witness and does not settle
R/free ownership. This illustrates why inference-only schemes cannot close
the compatibility gate. The yulang scratch fixture was restored to the
accepted identity result after this probe.

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

The next useful source evidence must come from an accepted source construction
or a complete saved graph view that connects the synthetic case to actual
lowering. It must align, for both member
roots, the same pre-finalization machine identity with:

1. published `scheme.quantifiers` and finalized recursive-bound variables;
2. occurrences in the finalized predicate, roles, and both recursive-bound
   sides; and
3. the per-use clone mapping or the source elaboration rule that determines
   whether that occurrence remains shared.

If no source program can express such a witness, the proof must say so and
derive the member-view ownership classes from the source-defined graph
construction instead. The next probe should identify a source path that
produces payload-free dependency cycles with mixed fetch classes, or establish
that such scheduler edges are unreachable for ordinary accepted programs. A
separate source trace should determine whether first-member prepasses lower a
shared variable before the next Q selection, and another should cover
root-local R/free ownership. Keep each result distinct from the synthetic
boundary-only Q/free witness. The
existing two-view example in the candidate proves only renaming algebra after
ownership classes are supplied. It does not close source-step adequacy, all
member-root observations, effects, principality, or final acceptance
equivalence. The scratch Oracle worktree and instrumentation are temporary
characterization only; no compiler code or test file was changed on this
branch.
