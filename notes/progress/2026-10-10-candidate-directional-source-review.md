# Directional source graph: independent construction review

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Status: reviewed level-one source and exact logical membership construction
Mode: M3, independent mathematical/compiler and specification reviewers
Pinned source/solver: `334fd359944cc1ecc5903e768c26349708e40fab`
Authority: current deferred Simple-sub instruction; existing candidate owners
Production or language/public-contract adoption: none

## Completed result

The [directional theorem](../theory/2026-10-10-candidate-directional-source-correspondence.md)
updates the actual-constructor argument after remote changed paired row bounds
to owner-side memberships and changed fresh initialization to explicit selected-
side restoration. The earlier [paired-owner theorem](../theory/2026-10-10-candidate-graph-call-correspondence.md)
remains valid at `280d399e`; it is not reused as a theorem of the changed kernel.

The new proof constructs the following results from the actual source path:

- SOURCE-LOCAL derives the level-one/generic invariant from startup, lexical
  formals, invocation allocation and actual incoming use levels.
- IDENTITY-EXTRUDE proves same-level extrusion returns the identical endpoint,
  traverses all four structural children correctly, and introduces no row,
  Function identity or source link. Transient scratch allocation remains.
- Active membership closure starts from the actual empty row lists and memo.
  Each insertion pairs with existing opposites before the worklist resumes;
  a later opposite insertion covers each newly enabled combination.
- CAPTURE constructs the least rooted component, including every reached
  membership's owner side, all four Function children and one typed row identity
  across polarities. Restricting the completed state to that actual forward
  closure preserves membership consequences.
- FRESH-ROUTE preallocates one actual fresh typed map and restores every source
  slot on its original owner side. The final root uses the actual incoming
  occurrence, cause and route transaction.
- REPLAY proves the logical membership set before root connection is exactly
  `M(C)`, where C is the constructor-derived captured set. Every induced
  membership is inside that closed image; every original member is explicitly
  inserted. Active root connection then preserves the membership invariant for
  later dependency-ordered captures.
- TERMINATION uses the finite same-level endpoint universe, finite memoized
  comparison expansions and finite explicit seed restoration. It does not
  certify unequal-level source copying or aggregate linear inference cost.

Neither a supplied saturated graph nor a completed local solution is a premise.
The closure induction follows the actual execution order from empty startup;
it does not identify an arbitrary idle solver with a saturated one.

## Exact changed behavior

At this pin, equal-level `e <= re` installs `e.upper re`. The old paired
`re.lower e` incidence is absent. The actual `invoke` demand still names the
same symbolic e, which then points to re. The pure callee Name evaluation row
ce may be outside the rooted capture because its `ce.upper re` is an incoming
predecessor with no other root path. No all-source-occurrence preservation or
semantic elimination of that omitted complement is claimed.

`Bound.side` now identifies the owning list. Filtering by owner, side and item
constructor recovers reached source endpoint-shape order/multiplicity. Runtime
replay may append extra logical duplicates, and original Function handles,
levels, full metadata, flags and causes are not an exact raw-record inverse.

Idle restoration samples an opposite count, then reads the current direct/exact
boundary while each induced comparison runs. The proof does not assume it
visits every originally sampled opposite slot. Exact set restoration follows
from constructor-derived closedness and unconditional insertion of all seeds;
it requires no fictitious stable-list law or unapproved code change.

## Independent review

Frozen theorem SHA-256:
`2bc8321c6bbfcc9296660a1583b7cfd0369de04c0f82de1828c5fca0fc54d96b`.

The mathematical/compiler referee read the complete proof and actual pinned
owners independently, including the new extrusion file, graph side capture,
restoration, worklist dispatch, source allocation and level changes. Verdict:
PASS, no BLOCKING, major or minor findings. Its main adversarial checks were
constructor-derived active closure, memo consequences, closed rooted restriction,
both inclusions of `M(C)`, disjoint source/receiving states and well-founded
induction over actual captures/routes. It explicitly rejected cache/diagnostic
or physical-state conclusions beyond the membership claim.

The specification auditor independently read the complete proof and exact
owners. Verdict: PASS, no findings. It verified directional owner selection,
source `e.upper re`, list-side reconstruction, same-level source envelope,
identity extrusion, no stable-scan premise, no hidden supplied saturation,
pre/post-receiver boundaries and the distinction from complete Call/public
semantics. Neither reviewer relied on passing fixtures or the remote code's
prior static review as a proof.

Both reviews completed before adjudication. No repair was required. The primary
changed only status and review/execution context afterward. The initial
post-review hash was `3f47c7628dc513a8df76cd555a26710605c203b37134261f1f49f6303c705c5e`.
A later record-only scope clarification distinguishes current worklist closure
from final initializer solving or a mandatory immutable let barrier, following
the user's correction. No mathematical claim or constructor changed. Final
hash: `acc924799ccfd7a8346221d864c7f1fd0414b86b80e8a259e95feba7bc7031c0`.

## Executed evidence and its limits

The [source fixture review](2026-10-10-candidate-graph-call-review.md) records the
actual parse/HIR/CandidateInference path, independent code reviews, repaired
assertion gaps, and both `invoke`/repeated-provider cases. After integrating
`334fd35`, the primary reran exactly the four new modules under
`shadow-apply-candidate` without changing their assertions:

```text
cargo test -p yu-solver --features shadow-apply-candidate --lib --   --test-threads=1 tests::complete_bound_constraints::   tests::deferred_call_constraints:: tests::kind_qualified_graph::   tests::candidate_graph_call::
```

PASS: 13 tests, 0 failed, 465 filtered, 0.02 seconds of execution; 14.25 seconds
compile, no warnings. Rust 1.99.0, one Cargo job, one test thread, incremental
compilation disabled, one test codegen unit and debug info disabled, with a
600-second timeout and the separate candidate target. These local verification
settings are not repository build-policy changes.

The two source cases inspect retained directional inequalities and the actual
fresh maps; they do not inspect paired incidence in graph mode. The older raw
helper cases execute the unchanged legacy branch with candidate graph mode off.
Those branches are not equated. No source fixture here traverses a younger-row
copy; the identity branch is the actual source case. No extra executable probe,
benchmark, broad workspace suite or numeric resource experiment ran for the
proof-only delta. Diff, link, dependency-blob and canonical-DAG hash checks are
owned by the primary.

## Closure and canonical status

This closes the changed constructor/membership correspondence in the stated
source envelope. It removes the old paired-incidence/replayed-pair assumptions
and the need for supplied graph/saturation/fresh-map witnesses at that seam.
It does not replace independent source obligations with scalar inequalities.

Full original CallMem/C0, JOINT_DEC, source-Generalize/public scheme correctness,
complete provider/world/receiver/protection/admission/future evidence and F5
cutover remain open. No canonical DAG status changes. A complete Call contract
has not been attached to this scalar graph by the present result, and set
closure is not a certificate for terminal-diagnostic replay or arbitrary active
predicates. General lexical levels, unequal-level source correspondence and
complete evidence placement remain separate from this level-one theorem.

The primary synchronized `tasks/current.md`, `notes/design/INDEX.md` and the
older source review's pending-delta pointer. No new source rule, pending
question choice or production change is part of this delta.

## Subsequent remote integration

Remote `801e16e` adds a separate generic local-source HIR sidecar. The primary
read the changed existing HIR entrypoints and its reviewed implementation record.
The four solver owners are byte-for-byte unchanged from the prior integrated
state. `lower_module_with_shadow_applications` leaves the new `local_source`
flag false; its parameter/depth policy is unchanged. The new entrypoint is not
called by the source fixtures and is not certified by this theorem. Existing
source/test paths were revalidated after this HIR merge. The first redirected
capture retained only dependency-compilation lines and is not counted as a
completed test result. A direct repeat of the exact same focused command
reported PASS: 13 tests, 0 failed, 465 filtered, 0.02 seconds execution, with no
warnings (the compiled target was current, 0.01 seconds Cargo completion).
No assertions or implementation were changed between those invocations.

The later `269f10a` remote changes only records, including the user's live-let
correction and the separate complete-source-spine packet. All compiler/test
owners remain unchanged; no Cargo rerun was needed for those records. The
primary preserved the remote additions and clarified that the theorem's
finite membership closure is not a prescribed local initialization schedule,
proof of satisfiability, or requirement to stop later cross-boundary refinement.
The reviewed research delta adds no live-let implementation or new constraint
solver before Simple-sub.
