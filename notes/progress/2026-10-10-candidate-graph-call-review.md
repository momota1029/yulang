# Actual source candidate Call graph: proof and execution review

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Status: reviewed bounded constructor theorem and executed source fixtures
Mode: M3; independent mathematical/compiler and specification review
Algorithm/source pin: `280d399e4e7e1ddcaacf2c1c6d8cf882ec88dc57`
Authority: current deferred Simple-sub correction; existing nonshipping constructors
Production/API or source-semantics adoption: none

## Completed construction

The [theorem](../theory/2026-10-10-candidate-graph-call-correspondence.md)
derives the graph from the actual candidate collector/session. It does not
assume a completed graph, solved formal/provider, successful satisfaction query,
complete source Call certificate or Source Generalize strategy.

- SOURCE-LOCAL derives every row's level-one/generic state from actual startup,
  DefinitionUse levels, invocation allocation and actual route/extrusion
  transitions in the finite supported empty-import candidate source envelope.
- CAPTURE proves the actual constructor computes the least rooted forward
  closure through all four Function ports and every direct/exact bound slot of
  each reached local row. Row kind distinguishes Value/Effect; polarity shares
  one row identity. An unknown formal's exact upper is retained.
- FRESH-ROUTE derives one injective typed map from actual fresh row allocation,
  preallocates it before reconstruction, preserves four-port shapes/cycles and
  submits every retained bound in sequence, then the actual receiving-root
  constraint. Distinct successful uses allocate disjoint local images.
- REPLAY proves retained logical scalar closure factors through that
  substitution, modulo equal structural shapes, before connecting the receiving
  environment. It is not a physical state, memo, cause or slot inverse.
- TERMINATION proves finite capture/reconstruction and scalar propagation from
  the actual finite endpoint universe and pair memo. Availability remains
  fallible. The successful constructor's linear reference/list-occurrence bound
  excludes solver closure, source collection and failure high-water accounting.

At the source pin, `invoke f = f 1` emits a demand using the real argument value
and evaluation effect, a fresh invocation-effect row and the real result row.
The same invocation row feeds the Apply/body evaluation effect. This removes
the need for a separately supplied graph, independent per-port fresh mappings
or a pure-effect representation prerequisite on this private graph path.
It does not remove complete Call, public source-Generalize or JOINT obligations.

The raw all-active snapshot is a stronger, independent research construction.
It is not made a mandatory prerequisite for this actual rooted candidate path.
The proof neither drops the uncaptured complement semantically nor certifies
mixed-anchor source eligibility. The source-local lemma avoids those branches
by deriving the actual present input envelope.

## Independent proof review and repairs

The full theorem was frozen at SHA-256
`89e44df5233c3fd34356e3635f966d4ad4ca8cff4091be105d135ca4b82a1e81`.
Both reviewers read that full artifact and actual owners pinned through `git
show`, without relying on producer confidence or test results.

The mathematical referee returned scoped PASS with no findings. It checked the
complete candidate graph owner, all source/route allocation and level changes,
actual Function/effect source incidence, every retained slot, one fresh map,
shape quotient, receiving-environment boundary, finite worklist/extrusion and
diagnostic completion, and the limited constructor cost claim.

The specification auditor returned scoped PASS with no BLOCKING/major finding.
One minor precision issue was accepted: the rule list must state terminal
extrema/incompatible dispatch takes precedence over bound installation.
`BottomPositive <= ValueRow` and `ValueRow <= TopNegative` install no exact
bound. After both reviews the primary added that explicit priority, preserving
the same factorization statement. The post-repair proof hash before status and
execution metadata updates was
`16d4fd434a1e431921ca908f9c734cba4a3a3b5125c1a0a7f9668359381b8767`.

Final status/link and executed-fixture metadata were then synchronized without
changing the mathematical scope. Final theorem SHA-256:
`56cc8d4d2d0260ffa01a3198a051a6da384f84ceaad209d8886d8c6504497018`.

## Test construction and independent code review

The new test-only module is
`crates/yu-solver/src/tests/candidate_graph_call.rs`, with a two-line
`shadow-apply-candidate` test hookup in `lib.rs`. There is no production API,
solver, parser, manifest, lockfile or expected language-output change.

Before writing, an independent spec preflight accepted the two source fixtures
as observations of existing nonshipping behavior. The producer initially
required the positive Lambda's argument-effect port to be a row; static primary
inspection caught that mismatch before execution or frozen review. The actual
constructor uses the Empty negative leaf there, distinct from the symbolic
invocation-effect row. The producer corrected only that mistaken assertion.

The complete formatted 326-line test was frozen at SHA-256
`9f428bb6f8a37ebe5b1debfacc0432225a7e1386f3852f7f9256e8e6c65a7ada`.

- Independent mathematical/compiler reviewer: scoped PASS with no findings.
  Checked directed bound reachability, opposite-polarity pivot at the same row,
  four-port sort/identity assertions, actual HIR/DefinitionUse ownership,
  source/fresh graph identity, within-use injection, cross-use freshness and
  integer support reaching the particular result roots.
- Independent specification reviewer: no BLOCKING/major findings. Two minor
  coverage gaps were accepted. Retained symbolic identity alone did not test
  absence of a prematurely supplied provider/Empty upper; the helper also only
  required some local Value/Effect rows, not that all fixture rows were local.

After both reports, the primary added three focused assertions: no positive
Function lower path into the captured formal; no retained path from the
invocation-effect row to an Empty upper; and all source graph rows local in
these particular empty-import fixtures. The original demand/incidence/map/result
checks remain. These are bounded scalar assertions, not full semantic provider
absence, satisfiability or source eligibility certificates. Both tests were
rerun after the repair and passed. Final helper SHA-256:
`4c3d7cb5f5930f510d1cd7f3f68cb656ed8cac46a1053be2359b2de57cfd014a`.

## Actual source execution

```yu
my invoke f = f 1
my first = invoke
my second = invoke
```

```yu
my id x = x
my invoke f = f 1
my first = invoke id
my second = invoke id
```

Each fixture uses actual syntax parsing, shadow application HIR lowering, empty
imports and `CandidateInference::solve`. No inference test walker supplies its
answer. The candidate must own the same HIR and report no recovered scalar
conflict. The tests inspect the captured `invoke` demand, integer argument,
shared result and symbolic invocation/body effect incidence. They also inspect
the actual source Name occurrences and their incoming routes.

For each use, every exported source row maps to one typed image in that use;
Value/Effect local images are disjoint between uses. Reborrowing the same
observation retains the same images. The second fixture checks both `id` and
`invoke` routes and an Int lower path into each actual `first`/`second` result.
Its final captured-graph observations are not a temporal equality comparison
of every slot before and after provider arrival.

The borrowed API does not expose installed fresh bound Terms. Map cardinality
or identity is not reported as executed preservation of all runtime incidence.
Anchor comparison code is present, but these all-local fixtures do not exercise
an anchor. `CandidateGraphExport` is not an ordinary `yu_types` closed scheme;
the test does not establish a certified public result or source admission.

## Verification and resource budget

Primary-only Cargo, Rust 1.99.0 (`b940084d7 2026-09-28`), one job, one test thread,
600-second command timeout, debug info disabled. Incremental compilation was
disabled and one test codegen unit used in the separate candidate target,
following the linker isolation recorded by the [raw graph review](2026-10-10-kind-qualified-graph-review.md).
No repository build configuration or compiler requirement was changed.

```text
cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_graph_call -- --test-threads=1
```

Initial frozen helper: PASS, 2 tests, 0 failed, 476 filtered, 0.01 seconds test
execution (13.22 seconds compile). After the two accepted minor coverage repairs:
PASS, 2 tests, 0 failed, 476 filtered, 0.01 seconds test execution (13.30 seconds
compile). No warnings appeared. A final combined run at the same source pin selected only
the four new test modules under `shadow-apply-candidate`: PASS, 13 tests, 0 failed,
465 filtered, 0.02 seconds. This revalidated the two complete-bound, five deferred
scalar/HIR, four raw-graph and two actual candidate source cases together. Only
the new module was formatted; primary diff/link/hash checks passed.

No workspace-wide suite, benchmark, standalone probe or numeric memory/cost
experiment ran. Static reviews are independent evidence; builds/tests are
root-owned deterministic evidence, not additional reviewers.

## Semantic and canonical status

No proof-DAG status changes. Original full CallMem/C0, JOINT_DEC, complete
Source Generalize/public export/fresh ordinary use and cutover remain open.
The present row-level constructor does not attach full receiver/whole-argument,
role/protection, correlated provider/world/carrier/context, production-only W/Z,
admission/license, output-dependent guarantee, pending/raw Resume/FutureUse or
unexecuted-suffix evidence. The theorem does not identify those conditions with
scalar inequalities or silently discharge them through a successful candidate.

At this pinned source state, all-one levels and in-place extrusion are not the general
Simple-sub polarity-copy/lexical-level correspondence. The pin records the
bounded owner; future source-level/anchor changes must revalidate the stated
premises. The current user instruction supplies no need to make a formal or
Call goal immediately satisfiable during generation, and this result adds none.

The primary synchronized `tasks/current.md` and `notes/design/INDEX.md`, including
the earlier reviewed raw-graph checkpoint. No pending question adoption is
included. The subsequently observed remote polarity-copy implementation changes
the bound owner/replay rules; this theorem remains explicitly pinned until its
separate constructive delta is reviewed. No assertion about unchanged replay
rules is inferred merely from rebasing these files.

## Latest remote revalidation

Before publication, remote advanced to `334fd359944cc1ecc5903e768c26349708e40fab`,
containing `e334940` polarity-copy extrusion and directional graph ownership.
The primary read the new 591-line owner, its replay/capture dispatch delta and
independent implementation record. Index/task conflicts were resolved by
preserving the entire remote additions and the reviewed research sections.
The new test assertions were not changed to fit that implementation.

On the rebased tree, the same focused four-module command passed all 13 tests,
0 failed, 465 filtered, 0.02 seconds execution (14.25 seconds compile), without
warnings. This is runtime revalidation of the new same-level source path and
unchanged legacy helpers. It does not execute a younger-row polarity copy.
The `280d399e` theorem remains pinned: new replay reinstalls the captured owner
side, not the old paired-edge seed submission. A constructive directional delta
is being proved independently before any latest-owner theorem is claimed.
