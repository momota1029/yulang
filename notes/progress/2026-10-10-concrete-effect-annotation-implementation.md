# Concrete/co annotation implementation checkpoint

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Committed source baseline: `a4ba1729bf352e450fcfc04c14e579181f5cbb09`
Authority: [concrete annotation gate](../design/2026-10-10-concrete-effect-annotation-implementation.md),
[selected hygiene policy](../design/2026-10-10-annotation-effect-hygiene-integration.md)
Mode: M3; three initial independent reviewers, two semantic/resource delta
reviewers, one final narrow conformance reviewer after runtime compilation repairs
Status: bounded private concrete/co implementation verified; broader goal active

## Implemented owners

HIR retains actual nullary effect declaration identities (module plus declaration
source key), exact declaration placeholders and whole-binding type annotations.
Resolution does not equate declarations by spelling. Unsupported declaration or
annotation forms do not gain permissions. Written annotation primitives are
interned at actual source Action construction before the term arena is sealed;
the owning integration test does not depend on unit-test-only preinterning.

The solver checks the body against the negative annotation target and publishes
the positive target, sharing annotation variables/views at the actual body level.
Covariant support is a structural type operand, not an emitted contribution.
Negative allowance accepts permitted atoms without tail backflow and forwards
unmatched atoms through its symbolic tail, preserving later checks. Member
diagnostics retain genuine annotation provenance separately from the rejecting
boundary. Actual contribution operands retain their independent instance and
source origin; no source operation execution producer is claimed here.

Capture, freshening, directional extrusion, SCC dependency/equality and rollback
preserve views and their executable tail dependencies. Per-operation remapping
shares one copied view per original identity/mapped-tail pair across support,
allowance and member operands. Distinct tails and uses remain distinct. Bound
origins and enqueue dependency edges support cached-root diagnostics without
changing the sole semantic typed-pair memo or replaying an unrelated earlier
conflict under a successful new request.

Incremental capacity accounting covers retained registries, diagnostic evidence
and live extrusion scratch, including nested samples and failure cleanup.
Tests inspect copied-view/atom counts, opposite-tail maps and injected-failure
peak coexistence/rollback. These are logical capacity assertions, not RSS or
timing evidence. Declaration lookup and allowance membership still scan their
finite vectors; normal solver propagation remains additional work.

## Review and repair closure

The [initial record](2026-10-10-concrete-effect-initial-review.md) preserves all
accepted findings. Fresh repairs closed compilation ownership, unrelated conflict
replay, repeated recovery scans, unbounded annotation construction, quadratic
view copying and missing extrusion scratch coexistence. Independent semantic and
resource delta reviews found no new blocking/major finding. Final conformance
delta closed the production primitive-registration panic and truthful fixture
stack scope. Existing semantic assertions/names were not weakened.

The owning contribution factory now returns its typed endpoint directly; this
fixes the new never-constructed warning without fabricating a source emission.
A feature-free HIR closure parameter was renamed to retain warning-free builds;
that final identifier-only edit required no new review or behavioral test cycle.

## Final focused checks

All Cargo commands used `RUSTC_WRAPPER=`, `timeout 180`, `--offline`, `-j 2`;
tests used `-- --test-threads=1`.

| Command after the common Cargo options | Result |
| --- | --- |
| `test -p yu-solver --features shadow-apply-candidate --test candidate_effect_annotation` | 5 passed |
| `test -p yu-hir --features shadow --lib module::source_annotation::tests` | 1 passed, 99 filtered |
| `test -p yu-solver --features shadow-apply-candidate --lib candidate_effect::tests` | 6 passed, 483 filtered |
| `test -p yu-solver --features shadow-apply-candidate --lib candidate_intrusion::tests` | 5 passed, 484 filtered |
| `test -p yu-solver --features shadow-apply-candidate --lib candidate_graph_call_` | 2 passed, 487 filtered |
| `test -p yu-solver --features shadow-apply-candidate --test simple_sub_local_source_retirement` | 5 passed |
| `test -p yu-solver --features shadow-apply-candidate --test shadow_apply_candidate` | 19 passed |
| `check -p yu-solver --all-targets --features shadow-apply-candidate` | Passed without warnings |
| `check -p yu-solver` | Final pass without warnings |

The focused matrix totals 43 passing tests. Initial failed runs remain in the
initial review record and this closure: missing syntax dependency, private error
field access, missing annotation primitive, and default-stack deep-fixture aborts
were diagnosed rather than accepted as expected behavior. Final checks use no
blanket stack environment override. Scoped diff checks passed. Workspace/backend
suites, timing benchmarks and full semantic proofs were not run. Benchmark
measurement budget consumed: zero samples/processes.

## Explicit parser stack boundary

The deep annotation fixtures parse, lower/check and drop artifacts in a dedicated
16 MiB worker, propagating assertion failure through join. They establish HIR's
depth-128 acceptance/depth-129 rejection on supplied parsed artifacts. They do
not establish default parser stack safety.

A separate primary scratch probe on an explicitly 2 MiB worker confirms the exact
owner: `parse_file` returns without recovery for 64 nested groups and 64 arrows,
but overflows during parsing 128 groups before returning a `ParsedFile`. The probe
is `/tmp/yulang-annotation-stack-primary/probe.rs`. One direct 16 MiB diagnostic
run of the HIR test passed; neither diagnostic is a performance measurement.
The parser owner needs its own bounded-stack/rejection design before claiming
that resource envelope for the source pipeline. No parser semantics or public
API was changed here.

## Remaining required work

Retire unused candidate F5 finalizer startup/finish through the
[typed lifecycle gate](2026-10-10-candidate-closed-lifecycle-retirement-next-gate.md).
Then implement authentic Unit and Act operation construction, preserving the
operation's inert request-carrier construction versus its separately justified
declaration-result execution consumer. Do not inject an emitted contribution
merely because an Apply has an operation-shaped callee.

Contravariant source subtraction still needs authentic attachment formation;
parameterized effects and broader annotations remain subsequent slices. Complete
Call, public transformed schemes and independent use, hygiene correspondence,
soundness/principality and default/target-branch F5 replacement remain required.
This checkpoint closes none of those through a scalar test or private graph.
