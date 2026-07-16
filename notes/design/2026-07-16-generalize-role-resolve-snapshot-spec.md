# Per-demand exact solve snapshots for generalization role resolution

Date: 2026-07-16

Status: draft staged feasibility and implementation design for Claude/user review. This document
does not approve implementation, does not change role-resolution semantics, and does not amend any
signed role-system specification.

## 1. Purpose

`analysis.generalize_resolve_roles` is currently the single largest phase in Yumark Markdown's
cold compile: 1.871 seconds, or 34.83% of a 5.372-second total. Comparable Yumark HTML,
repository-std-only, and showcase runs spend only approximately 7-11 milliseconds in the same
phase.

A completed read-only investigation localized one exact duplicate solve inside the generalization
loop. The target is deliberately narrow: retain the exact pure result of one normalized role demand
within one root's generalization, and reuse it only when every solver input relevant to that result
is exactly unchanged. The intended production rule is:

```text
snapshot = (
  constraint_epoch,
  role_solve_supplemental_epoch,
  post_floor_normalized_main,
  normalized_demand,
  candidate_table_guard,
  exact_recursive_solve_result,
)

same constraint and role-solve-supplemental epochs
and same post-floor normalized main
and same normalized demand
and unchanged candidate table
  => the pure unique-candidate/prerequisite solve result may be reused

current applied-set membership
  => always evaluated again against current state
```

Every comparison above is exact. Any missing guard, ambiguous state, failed comparison, budget
failure, or inability to prove candidate-table stability is a cache miss and runs the unchanged full
solver. A false miss costs time. A false hit can change a generalized scheme and is a correctness
bug.

This project does not try to prevent the normalized role tree from expanding. It also does not
reuse the other work repeated by a generalization-loop restart. Those are separate projects with
different size, risk, and correctness boundaries.

## 2. Verified diagnosis

### 2.1 Markdown and HTML differ because of generalization order, not role volume

The Markdown regression is not caused by Markdown having intrinsically more role work. It is an
ordering coincidence.

When root `proof` (`DefId(167)` in the observed Markdown trace) generalizes, the `cons_cell`
role-implementation candidate (`DefId(131)`, member `DefId(132)`) already has its prerequisites
registered. Resolution therefore walks 71 recursive prerequisites to depth 14 and performs 2,272
candidate scans.

HTML reaches the equivalent candidate before those prerequisites are registered. Its walk stops
after one prerequisite and 32 candidate scans. The `DefId` values identify this trace; they are not
stable cache identities and must never become fixture- or ID-specific production conditions.

The first Markdown walk is not the expensive waste. Resolving all 71 prerequisites takes only
approximately 11 milliseconds. It is necessary work for the state observed at that iteration.

### 2.2 Structural expansion makes a later duplicate expensive

After the first resolution, the normalized role representation grows by approximately 95.3 times
under the investigation's Debug-size proxy: about 33 KB becomes about 3.16 MB. This is not a claim
about allocator-retained bytes. It is a structural-size proxy showing that a shared, deeply nested
`cons_cell` shape is cloned into an owned `CompactType` tree at every occurrence.

The `proof` root restarts its generalization loop three times. The relevant sequence is:

| Iteration | Observed normalized role state | Role solve | State change and consequence |
| --- | --- | --- | --- |
| 2 | about 33 KB; 71 prerequisites | about 11 ms | adds 179 new upper-bound facts and must restart |
| 3 | about 3.159 MB | about 0.78-0.80 s | the `cons_cell` prerequisite is now unresolved; inserting it as a residual predicate into the owner role table changes state and must restart |
| 4 | about 3.163 MB; two roles | about 0.95-0.99 s | resolves to zero new resolutions |

Iterations 2 and 3 are necessary under the current algorithm because each changes state. Iteration
4 is the bounded target. A direct exact comparison between iterations 3 and 4 found all of the
following unchanged:

- the constraint epoch;
- the role-solve supplemental epoch;
- the post-floor main `CompactRoot`;
- the previous normalized demand.

Iteration 4 therefore re-executes an already fully processed solver state after the iteration-3
state change has been incorporated. The candidate-table guard remains an explicit precondition of
the proposed cache and must be validated across the generalization boundary in Stage 0; it is not
silently inferred from the four comparisons above.

### 2.3 Necessary work versus removable work

This distinction is a project invariant:

- the initial depth-14, 71-prerequisite walk is necessary and cheap;
- the iteration-2 upper-bound publication is necessary;
- the iteration-3 residual-predicate insertion is an actual state change and is necessary;
- only a later per-demand invocation with all exact guards unchanged is reusable;
- any demand whose guards differ still takes the full solver path.

The optimization must not suppress a restart, coalesce residual predicates, weaken role matching,
or redefine an unresolved prerequisite as resolved. It removes only a proven duplicate invocation.

### 2.4 Existing exact-reuse mechanisms do not cover this call

The exact-reuse gates introduced by `ae6afc58` and `cfa017f6` apply to final post-loop filtering.
They do not prevent the solver re-invocation between generalization iterations 3 and 4. Reusing or
extending those gates by name is not evidence that this solver boundary is covered; the Stage 0
input inventory and Stage 1 shadow oracle remain required.

## 3. Project boundary and correctness invariant

### 3.1 Scheduling unit and lifetime

The scheduling unit is one exact normalized role demand within one invocation of one root's
generalization loop. The cache is loop-local:

- it is created when generalization of the root begins;
- it may retain entries only across restarts of that same root's loop;
- it is cleared when that root finishes, aborts, or leaves the generalization path;
- it is never serialized or shared across roots, SCC lifecycles, analysis sessions, or artifacts.

The normalized demand itself is the exact identity. Version 1 does not introduce a stable global
`DemandId`, path/name lookup, or heuristic correspondence between different demand shapes.

### 3.2 Exact-reuse invariant

Let a full solve at the existing post-floor role-resolution boundary observe:

- `E`: the current constraint epoch;
- `A`: the role-solve supplemental epoch covering solver-observable mutations deliberately absent
  from the legacy epoch;
- `M`: the exact post-floor normalized main `CompactRoot` consumed by the solver;
- `D`: the exact normalized demand consumed by the solver;
- `C`: an exact witness that the role-impl candidate table and recursive prerequisite definitions
  relevant to solving `D` have not changed; and
- `R`: the exact pure unique-candidate and recursive-prerequisite result, including deterministic
  unresolved, ambiguous, cycle, and nested-prerequisite outcomes represented by the current solver.

A later solve may use `R` only when current values `E'`, `A'`, `M'`, `D'`, and `C'` satisfy:

```text
E' == E && A' == A && M' == M && D' == D && C' == C
```

Equality of `M` and `D` is structural equality of the actual normalized values, not equality of a
Debug string, allocation address, size, hash, or summary. A hash may reject unequal inputs before a
structural comparison, but a hash match is never sufficient for reuse.

Capture and comparison occur at the same existing post-drain, post-floor solver boundary. If
pending work, an incomplete drain, or an uncertain epoch boundary makes the current state
ambiguous, the entry is ineligible and the full solver runs.

### 3.3 Applied membership is live state, not snapshot state

`applied`-set membership is intentionally not copied into the reusable result. On every cache hit,
the current production disposition/application step evaluates every returned resolution key
against the current `applied` set.

This yields the required split:

```text
exact recursive candidate solve: reusable under E/M/D/C/A equality
current applied membership and state publication: always live
```

The cache must not replay an old `newly-resolved`/`already-applied` classification. It supplies the
same pure resolution tree that a full solve would supply at the current boundary, then lets the
unchanged current-state logic classify and publish it. Residual-predicate insertion, new upper
bounds, and any other state-changing disposition remain governed by current state.

Stage 0 must verify that the chosen cache boundary contains no hidden `applied` membership read that
changes construction of the recursive result itself. If such a read exists, the boundary must move
so membership is reevaluated, or the project stops for a size/risk revision. Treating old applied
state as part of an exact result is not an allowed shortcut.

### 3.4 Candidate-table guard

Version 1 must use one of two exact mechanisms:

1. a candidate-table generation captured in the snapshot and advanced by every effective candidate
   addition, removal, replacement, ordering/visibility change, or prerequisite extension/change; or
2. an executable invariant that makes the complete candidate table immutable throughout one root's
   generalization, with all mutation APIs structurally unable to run in that interval.

A comment or debug-only assertion is not an immutability mechanism. If the table can change, the
generation must cover direct and indirect mutation, including prerequisite changes reached by the
recursive walk. If neither mechanism can be made complete within M/medium scope, stop before shadow
implementation and revise the project estimate.

## 4. Proposed mechanism

### 4.1 Loop-local snapshot contents

Conceptually, each entry contains:

```rust
struct PerDemandExactSolveSnapshot {
    constraint_epoch: ConstraintEpoch,
    role_solve_supplemental_epoch: RoleSolveSupplementalEpoch,
    post_floor_main: CompactRoot,
    normalized_demand: /* existing normalized demand type */,
    candidate_guard: CandidateTableGuard,
    result: /* existing exact recursive role-solve result */,
}
```

The names are illustrative. The semantic fields are mandatory. The implementation should use the
current solver's result type where possible rather than creating a second role-resolution model.
The result must preserve all data and deterministic ordering needed by the unchanged downstream
disposition step.

The snapshot contains the unique-candidate result and its complete recursive prerequisite result.
It also preserves the current solver's unresolved, ambiguous, and cycle outcomes when those occur
inside that tree. It does not contain a final generalized scheme, a copied applied set, a replay log
of mutations, or an instruction to skip the generalization restart.

### 4.2 Lookup and publication order

The intended path is:

```text
normalize/floor main through the unchanged path
normalize demand through the unchanged path
read current constraint and role-solve-supplemental epochs plus candidate-table guard

exact snapshot match?
  no:
    run the unchanged full recursive solve
    retain its pure result with E/M/D/C/A, subject to the cache budget
  yes:
    reuse the stored pure result

in both cases:
  reevaluate applied membership against current state
  run the unchanged disposition/publication path
  preserve the existing restart decision and ordering
```

The cache consumes normalized values the production path already creates. It must not add another
normalization, compaction, traversal of the candidate graph, or solve-until-stable loop merely to
construct a cache key. Any auxiliary hash must be computed from already available data or justified
by Stage 0 measurements, and it remains only a prefilter for exact equality.

Publishing a snapshot occurs only after a full pure solve has completed successfully. A panic,
early abort, partial recursive result, budget failure, or uncertain candidate guard publishes no
entry. Replacement and eviction can only cause future misses; they may never synthesize a hit.

### 4.3 Cache ownership, bounds, and memory discipline

The cache is bounded even though its lifetime is short. The Markdown trace demonstrates why: an
exact key can retain a structurally large owned `CompactRoot`, and a naive snapshot clone could add
material memory and equality cost even while saving solver time.

Stage 0 measures:

- entries retained per generalization root;
- structural units and retained bytes for exact main, demand, and result values;
- cloning/retention cost;
- exact equality cost on hits and misses; and
- peak loop-local cache memory over the representative fixtures.

Absolute entry and retained-byte caps are **TBD, to be measured and approved in Stage 0**. If an
insertion would exceed an approved cap, version 1 clears or disables reuse for the current root and
runs full solves. It does not replace exact values with a lossy fingerprint, grow an unbounded
cache, or silently raise the cap.

Using existing ownership to avoid an unnecessary clone is allowed if it does not change the
`CompactType` representation or solver semantics. Introducing global interning, DAG conversion, or
a new shared compact representation is not an implementation technique for this project.

### 4.4 Failure policy

The full solver is the fallback and the oracle. The cache is ineligible when:

- either constraint epoch differs or cannot witness unchanged state at the exact boundary;
- the post-floor main differs structurally;
- the normalized demand differs structurally;
- the candidate generation differs, overflows, is unavailable, or its immutability invariant is
  not active;
- the entry is partial, stale, outside the current root, or over budget;
- exact equality cannot be completed;
- shadow verification reports any result, disposition, state-delta, or scheme mismatch; or
- a future solver input is discovered which is absent from the snapshot contract.

There is no source diagnostic for a miss. Failure to reuse is a performance event only.

## 5. Relationship to nearby projects

### 5.1 Generalization iteration reuse is related but separate

The same restarts also repeat `generalize_collect_roles` and
`generalize_collect_dominance`, costing approximately 330-436 milliseconds per repeat iteration in
the completed investigation. That is the previously identified **generalization iteration reuse**
project.

It is not approved and is not part of this design. It needs a broader reachability and mutation
frontier, must decide which prepass outputs remain valid across a restart, and is estimated at
L-XL/very-high risk. This per-demand project must not retain role-collection or dominance results,
skip a loop iteration, or become a general generalization scheduler.

### 5.2 Owner-level dirty scheduling is not the implementation substrate

The production owner-level dirty scheduler operates inside forced method-role passes and uses
`SelectionUse.parent` plus a session-wide typed mutation contract. This project operates inside one
root's generalization loop, where the exact normalized main and demand already provide a smaller
reuse boundary.

Reusing the owner scheduler, extending its mutation vocabulary into generalization, or sharing its
records would broaden the project and violate the existing solver invariant requiring a separate
design review before owner scheduling expands into generalization.

### 5.3 Constraint replay deduplication is not implicated

The 2026-07-16 constraint-replay investigation found that its high duplicate counters describe
already-rejected transitive-closure rediscovery, not removable local replay work. This snapshot
project neither changes constraint evidence nor suppresses replay. Paired constraint and
supplemental epoch equality is a reuse guard, not a new replay policy.

## 6. Staged implementation plan

Sizes use the repository's `S / M / M-L / L / L-XL` scale. Risk uses
`low / medium / medium-high / high / very-high`.

The planned project is shorter than owner-level dirty scheduling because it is loop-local and uses
exact existing values rather than a cross-table mutation journal. No stage starts merely because it
appears here. The design must first be accepted; production activation receives a separate explicit
review after shadow evidence.

### Stage 0: broader characterization and exact-input contract lock

- Size: S.
- Risk: low.
- Approval class: characterization only; no production behavior change.
- Changes: extend observation-only tracing across more roots and the complete representative
  fixture set. Reproduce the iteration-3-to-4 equality witness, inventory every input read by the
  recursive solver, validate the paired constraint-epoch boundary, decide candidate generation versus
  enforced immutability, and measure equality/retention costs and cache cardinality. Establish
  numerical performance and memory gates from controlled measurements; values not already in this
  document are TBD until this stage.
- Exit criteria:
  1. the Markdown `proof` trace reproduces the exact epoch/main/demand equality and the necessary
     versus wasted iteration split, or drift is explained before proceeding;
  2. the same observation runs over Markdown, HTML, repository-std-only, showcase, and the required
     rename/module-move variants, with per-root and per-demand counts rather than only the one
     `DefId(167)` trace;
  3. every mutable input capable of changing the recursive candidate result maps to `E`, `M`, `D`,
     `C`, or the Stage 0-selected supplemental `A`; no unclassified solver input remains;
  4. equality of `E` and `A` is proven to cover every solver-observable constraint mutation at
     this boundary, including the absence of pending work and events;
  5. candidate-table immutability is mechanically established, or a complete generation contract
     and its mutation inventory are selected;
  6. the exact boundary between pure recursive result and live applied/disposition state is
     documented and tested;
  7. equality cost, snapshot retention cost, peak entries, and retained bytes are measured, and
     absolute caps plus activation performance/no-regression gates receive explicit approval;
  8. repeated exact states occur beyond a single hard-coded fixture identity, or the project stops
     as a one-off optimization; and
  9. if completing the input contract requires a session-wide journal, compact-representation
     redesign, or iteration-wide prepass reuse, stop and revise size/risk before Stage 1.

### Stage 1: exact snapshot implementation in shadow mode

- Size: M.
- Risk: medium.
- Approval class: inactive/shadow implementation; production continues to use full solve results.
- Changes: add the bounded loop-local snapshot, exact-key comparison, candidate guard, live applied
  filtering, miss reasons, and an independent shadow path. At every would-be hit, compute both the
  cached and full recursive resolution trees from the same pre-disposition state and compare them
  exactly. Compare cache-enabled and always-full-solve final schemes in isolated paired runs so one
  branch's mutations cannot contaminate the other.
- Exit criteria:
  1. cached and full recursive resolution trees are exactly equal at every would-be hit over the
     complete acceptance set;
  2. under the same current applied set, the two paths produce equal disposition sets and equal
     state deltas for unresolved, ambiguous, newly resolved, and already-applied cases;
  3. final generalized schemes, residual predicates, diagnostics, selections, and lowering/runtime
     results are exactly equal in paired runs;
  4. every epoch/main/demand/candidate mismatch demonstrably takes the full solver path;
  5. nested prerequisite, shared prerequisite, ambiguity, and cycle adversaries have zero shadow
     mismatches;
  6. cap exhaustion, incomplete entries, generation overflow, and unavailable guard state all fail
     closed to full solves;
  7. shadow instrumentation does not change the production-selected result or restart order;
  8. no cache key depends on path, module name, function name, fixture name, raw Debug text, or
     `DefId` constants; and
  9. the Stage 0 performance and memory gates still appear attainable after measuring real lookup,
     equality, storage, and fresh-applied-filtering overhead. Otherwise stop before activation.

#### Stage 1 complete (2026-07-16): exact shadow parity and gate re-measurement

Stage 1 landed in three test-only slices: `0a2d52b1` added the exact shadow oracle,
`2a8a7782` added the bounded fail-closed cache and adversaries, and `4c51d287` completed the
acceptance-set and isolated-paired production-parity coverage. Production still unconditionally
uses the full-solve result. Stage 2 has not started and still requires the separate explicit human
decision specified below.

All nine Stage 1 exit criteria are met:

1. The complete nine-case acceptance set produced 1,019 would-be hits, 1,019 exact recursive-result
   matches, and zero result mismatches.
2. Focused unresolved, ambiguous, newly-resolved, and already-applied witnesses exercise live
   applied filtering. The acceptance run reported zero disposition, state-delta, or full-path
   mismatches.
3. Isolated shadow-off/shadow-on runs matched finalized schemes, residual predicates, diagnostics,
   unresolved selections, generalization restart/SCC order, poly surfaces, compiled lowering
   surfaces, and runtime-lowered surfaces exactly. The two branches use separate lowering sessions.
4. The explicit `E/A/M/D/C` miss classifications all retain the unconditional full solve. The
   acceptance set observed 113 epoch, 2,011 demand, and 964 lifecycle misses. The full-solve call
   is structurally upstream of all shadow comparisons, so supplemental-epoch/main/candidate
   mismatches cannot suppress it either.
5. Nested and shared prerequisites, ambiguity, and cycle termination have focused exact-result and
   live-application witnesses, with zero shadow mismatches.
6. Entry/byte cap exhaustion, incomplete entries, generation overflow, unavailable guards,
   unwitnessable epochs, and non-quiescent boundaries all clear or disable reuse and fail closed.
7. The instrumentation is `#[cfg(test)]`-gated, the production-selected result remains the
   unconditional full-solve result, and isolated parity fixes restart counts and SCC event order.
8. The exhaustive retained-entry identity audit fixes the key to structural `E/A/M/D/C` fields;
   path/name/fixture strings, Debug text, and `DefId` constants are reporting data only.
9. The fresh measurements below leave the approved absolute caps with substantial headroom and
   show that the measured hit/storage costs remain below the full-solve time available to remove.

A fresh `RUSTC_WRAPPER= cargo build --release -p yulang` succeeded. The established one-shot
no-cache release measurements were:

| Fixture | Internal total | `analysis.generalize_resolve_roles` | External wall | Max RSS |
| --- | ---: | ---: | ---: | ---: |
| Yumark Markdown | 5.775 s | 1.930 s | 5.90 s | 448,568 KiB |
| Yumark HTML | 1.153 s | 12.3 ms | 1.25 s | 216,604 KiB |
| Repository std only | 1.034 s | 7.3 ms | 1.08 s | 200,164 KiB |
| Showcase | 1.150 s | 8.3 ms | 1.21 s | 203,944 KiB |

These release measurements contain no Stage 1 snapshot work: the module, session state, and
generalization wiring are all compiled out outside `cfg(test)`. They are current production timing
context, not a shadow-on/shadow-off release A/B. The Markdown total and role phase remain in the
same broad range as Section 1's earlier one-shot values; the differences cannot be attributed to
test-only Stage 1 code.

The shadow overhead was therefore re-measured through the acceptance-set test's own instrumentation.
Across all nine cases, the would-be-hit full solves accounted for 1.733425 s. The explicitly timed
snapshot dimensions were 13.537 ms for demand plus `E/A/M/C` lookup/equality, 47.309 ms for exact
result equality, 699.150 ms for two fresh-applied applications per hit, 18.552 ms for disposition
comparison, 0.333 ms for state-delta comparison, 104.663 ms for 2,124 snapshot clones, and 1.943 ms
for retention accounting. Their 885.487 ms sum is below the measured 1.733425 s full-solve
opportunity. It is not a claim about total test wall overhead: Debug-size formatting and report
allocation are not separately timed. A Stage 2 production hit should also be cheaper than this
shadow path because it will not perform the oracle result/disposition/state comparisons and will
apply the retained result once rather than twice.

Peak retention was 6 entries and 20,653,144 Debug-proxy bytes against the approved absolute caps of
64 entries and 128 MiB (134,217,728 bytes), with zero acceptance-set cap fallbacks. The retained-byte
peak is 24 bytes above Stage 0's 20,653,120-byte observation, exactly consistent with the three
Markdown `proof` snapshots each replacing the original 8-byte raw candidate generation with the
16-byte fail-closed generation/unavailable/overflowed guard; it is not compact-tree growth and still
leaves about 6.5x byte headroom. This proxy is deliberately not allocator-retained RSS.

Section 8 records qualitative activation requirements but still leaves numerical release
improvement/no-regression thresholds as TBD. Stage 1 criterion 9 is satisfied as an attainability
gate by the measured mechanism margin and cap headroom; Stage 2 planning must turn those TBDs into
an explicitly approved same-time alternating release gate before production activation. This
closeout does not authorize or begin Stage 2.

### Stage 2: fail-closed production activation

- Size: S-M.
- Risk: medium.
- Approval class: separate explicit human sign-off immediately before behavior activation.
- Changes: allow an exact hit to bypass the full recursive solve while retaining the unchanged
  normalization, current applied filtering, disposition/publication, restart order, and full-solve
  fallback. Keep an explicit always-full-solve control for rollback and paired verification. Re-run
  the approved release performance gates with same-time alternating controls.
- Exit criteria:
  1. the representative Markdown iteration-4 call becomes an exact cache hit and does not invoke the
     full recursive solver;
  2. the independent shadow/full-solve control reports zero resolution-tree, disposition,
     state-delta, and final-scheme mismatches over the complete acceptance set;
  3. every forced-miss and budget adversary still executes the unchanged full solver;
  4. Markdown meets the Stage 0-approved `analysis.generalize_resolve_roles` and cold end-to-end
     improvement gates;
  5. HTML, repository-std-only, showcase, ordinary small/non-role controls, and rename/module-move
     variants stay within the Stage 0-approved no-regression budgets;
  6. hit overhead is lower than the avoided full solve and miss overhead remains within the
     approved budget;
  7. peak loop-local memory stays within the approved absolute entry/byte caps;
  8. source output, diagnostics, generalized schemes, and runtime results match always-full-solve
     mode; and
  9. no implementation work from the generalization-iteration-reuse or compact-DAG projects has
     been folded into activation.

### Stage 3: hardening, cleanup, and closeout

- Size: S.
- Risk: low-medium.
- Approval class: explicit review after production evidence.
- Changes: retain independent correctness controls, remove only instrumentation proven redundant,
  finalize metrics and invariant documentation, exercise the rollback path, and record follow-up
  opportunities without implementing them.
- Exit criteria:
  1. the exact shadow oracle and always-full-solve control remain available as continuing assurance,
     not one-time scaffolding;
  2. cache state is proven absent after every root completion, abort, and session finish path;
  3. absolute caps and fail-closed behavior have focused regression tests and match production
     defaults;
  4. a rollback drill disables reuse without reverting unrelated generalization or role-solver
     fixes;
  5. telemetry distinguishes full solves, exact hits, miss reasons, cap fallback, and shadow
     mismatches without changing source diagnostics;
  6. realized solve-time and end-to-end gains are recorded separately from hit count;
  7. no exact comparator, candidate guard, or independent oracle is removed without a dedicated
     redundancy proof; and
  8. the 95.3x compact-tree expansion and generalization iteration reuse remain explicitly deferred.

## 7. Test plan and acceptance oracles

Correctness tests compare the cached path with the unchanged full solver. Performance counters are
reported separately because a valid hit intentionally changes solve-call and candidate-scan counts.
No expected type or scheme may be rewritten merely to match cached output.

### T0: exact-key hit parity

Construct a demand where both epochs, post-floor main, normalized demand, and candidate guard are
exactly unchanged. Solve once, then compare cached and full paths from the same current state. Require exact
recursive resolution-tree equality, disposition-set equality, state-delta equality, and final-scheme
equality.

Cover repeated results which are resolved, unresolved, and ambiguous. A successful cache lookup is
not sufficient unless the independent full solve produces the same exact result.

### T1: paired constraint-epoch miss matrix

Keep main, demand, and candidate table unchanged while changing either `E` or `A` through its
corresponding solver-observable constraint mutation. The cache must miss. Include a control where
all guards stay unchanged and the same entry hits.

If a future observable constraint mutation advances neither selected epoch, Stage 2 is blocked;
the test expectation must not be weakened to accept reuse.

### T2: structural main and demand miss matrix

Test the two structural guards independently:

- same epoch/demand/candidates but a changed post-floor main;
- same epoch/main/candidates but a changed normalized demand;
- structurally equal values with different allocation identity, which must remain eligible; and
- values with equal size or any equal hash prefilter but different structure, which must miss.

These tests establish structural equality rather than pointer, Debug-text, size, or hash identity.

### T3: candidate-table change matrix

Under the generation design, candidate addition, removal/replacement where supported, visibility or
ordering change where observable, and prerequisite extension/change must advance the guard and force
a full solve. At minimum, candidate addition and prerequisite extension are mandatory focused cases.

Under the immutability design, tests must prove that those mutations cannot occur while the root
generalization guard is active and that attempting to bypass the guarded API fails closed. The two
designs are alternatives; lack of tests is not an immutability proof.

### T4: live disposition and applied-membership matrix

For the same cached recursive result, compare cached and full paths under current state containing:

- an unresolved result;
- an ambiguous result;
- a newly resolved key absent from `applied`;
- the same key already present in `applied`; and
- mixed recursive results where one key is new and another is already applied.

The snapshot-time applied classification must not influence the result. The cache and full solver
must produce the same current disposition set, residual insertion behavior, upper-bound publication,
restart decision, and final scheme.

### T5: recursive prerequisite and cycle matrix

Cover a unique candidate with multiple nested prerequisites, shared prerequisites, a failed nested
prerequisite which becomes residual, an ambiguous nested prerequisite, and existing cycle-termination
cases. Exact comparison includes the complete recursive tree and deterministic order, not only the
top-level candidate.

### T6: restart and root-lifecycle regression

Preserve the Markdown `proof` trace as a regression witness without making its names or observed
`DefId`s part of cache behavior. Assert that the state-changing iterations still restart, the later
exact duplicate is reusable, and the cache is cleared when the root finishes or aborts. Add a root
with no reusable repeat and require full solves throughout.

### T7: shadow-mode full-pipeline parity

Shadow mode computes both the cached and full resolution trees and compares them exactly before
production state is mutated. Paired isolated sessions then compare final generalized schemes and
the relevant source-visible outputs exactly. One branch may not serve as its own oracle or observe
mutations already published by the other branch.

### T8: representative and metamorphic fixture set

The acceptance set is:

- Yumark Markdown;
- Yumark HTML;
- repository std only;
- showcase;
- ordinary small-role and non-role controls selected in Stage 0; and
- rename and module-move variants whose structured resolution targets remain equivalent.

Rename/module-move parity proves that reuse depends on normalized structure and solver state, not
surface names, paths, fixture identity, or the trace's raw `DefId` values.

### T9: fail-closed and budget adversaries

Exercise missing entries, partial entries, either epoch mismatch, main mismatch, demand mismatch,
candidate guard mismatch/unavailability, generation overflow, cap exhaustion, and cache-lifetime escape. Every
case must run the full solver and preserve source behavior. A cap test must also show that the cache
does not replace exact values with a lossy key after exhaustion.

## 8. Performance, budget, and no-heavy-fixpoint audit

Activation is acceptable only if:

- lookup uses the normalized main and demand already produced by the current iteration;
- a hit performs exact guards, fresh applied filtering, and the unchanged disposition step, but no
  recursive candidate solve;
- a miss performs at most bounded key/cache overhead before the unchanged full solve;
- the cache is bounded by approved absolute entry and retained-byte caps;
- cap failure disables reuse and never increases an unbounded limit;
- no second production solve is added outside shadow verification;
- no additional generalization fixed-point loop is added;
- no role collection, dominance collection, or compact-DAG construction is hidden in cache lookup;
- no rigid/protected variable, blocked pair, or through flag is introduced;
- no missing input is represented as `Any`, `Never`, predicate deletion, or cached success; and
- hit count, role-solve time, and end-to-end time are measured and reported separately.

### Stage 2 numerical release gates (approved by Claude/user on 2026-07-16)

The following thresholds were approved before the separate Stage 2 production-activation work
began. They use only the Stage 0/1 measurements above and the original diagnosis: Markdown's
removable iteration-4 solve was approximately 0.95-0.99 seconds of an approximately
1.87-1.93-second `analysis.generalize_resolve_roles` phase and an approximately 5.3-5.9-second full
compile.

Measure five same-time alternating release pairs per fixture, reversing enabled/always-full-solve
order between successive pairs. Each command uses the same no-cache route and fresh process
conditions. The gate compares arithmetic means from the paired run set; external process wall time
and max RSS are reported as supporting observations, while the compiler's internal
`run.build_poly` / `check total` and phase timings are the release decisions.

- Yumark Markdown must improve its mean internal cold `run.build_poly` / `check total` by at least
  10% with exact snapshot activation enabled relative to always-full-solve mode.
- Yumark Markdown must improve its mean `analysis.generalize_resolve_roles` time by at least 35%.
- Yumark HTML, repository-std-only, and showcase must each stay at or below a 2% mean internal cold
  `run.build_poly` / `check total` regression. Improvements are allowed; the bound is one-sided.
- Peak loop-local retention must remain within the already approved absolute caps of 64 entries and
  128 MiB of the Stage 0/1 Debug-size proxy, with no cap fallback in the four release fixtures.

The 10% end-to-end threshold asks the activation to retain at least roughly 0.53-0.59 seconds of the
0.95-0.99-second duplicate-solve opportunity. The 35% phase threshold asks it to remove at least
roughly 0.65-0.68 seconds from the 1.87-1.93-second role phase. Both leave explicit room for exact
lookup/equality, bounded snapshot retention, result access, and ordinary timing noise, but reject an
implementation which consumes most of the measured opportunity. Stage 1 measured 1.733425 seconds
of would-be-hit full solves across the acceptance set versus 13.537 milliseconds of key
lookup/equality and 104.663 milliseconds of snapshot cloning; its heavier shadow-only result,
disposition, and state comparisons do not run on an ordinary Stage 2 production hit.

The 2% control bound follows the measured opportunity distribution rather than assuming a speedup:
HTML, repository-std-only, and showcase spent only 7.3-12.3 milliseconds in the role phase and
showed near-zero would-be-hit activity for this duplicate pattern. Activation should therefore be a
wash on their approximately 1.03-1.15-second internal totals. A larger regression is evidence of
fixed miss-path or lifecycle overhead and stops activation even if Markdown passes. Percentage
gates are deliberately not applied to those fixtures' 7-12-millisecond role subphases because such
small denominators make them a noise amplifier; their end-to-end bound is the fixed-overhead gate.

Failure of either Markdown improvement threshold, any individual control-fixture no-regression
threshold, or either absolute memory cap stops activation. A high hit count alone cannot override a
failed time or memory gate, and the thresholds must not be weakened after observing Stage 2 output.

### Preliminary Stage 2 activation verification (2026-07-16; superseded by Slice C)

This five-pair run exposed the production hit-count concern which triggered the more rigorous
Slice C diagnosis. Its implementation and timing results are retained as the pre-fix record, but
they are not the final Stage 2 decision data. Correctness verification passed before performance
measurement. The isolated production versus
always-full-solve parity test covered Markdown and HTML in separate sessions and preserved final
schemes, residual predicates, diagnostics, selections, restart/SCC order, lowering, poly output,
and runtime output exactly; production recorded exact hits and fewer full solves. The independent
test-only shadow audit remained enabled as a full-solve assurance path and again reported 1,019
would-be hits, 1,019 exact matches, and zero result, disposition, state-delta, or full-path
mismatches. `cargo test -p infer --lib -- --test-threads=1` finished with 831 passed and only the
five pre-existing `mark_expr_block_*` failures.

The release binary was rebuilt with `RUSTC_WRAPPER= cargo build --release -p yulang`. Each fixture
then ran in a fresh process with cache disabled. Five pairs used enabled/always-solve order for odd
pairs and always-solve/enabled order for even pairs. Markdown, HTML, and showcase used the runtime
route; repository-std-only used the same repository std plus trivial-root runtime route represented
by `tests/yulang/support/empty.yu`. The table reports arithmetic means of the compiler's internal
timings; a positive change is an improvement and a negative change is a regression.

| Fixture | Enabled total | Always-solve total | Total change | Enabled role phase | Always-solve role phase | Role change | Gate |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| Yumark Markdown | 7.6860 s | 7.6344 s | -0.676% | 2.7974 s | 2.7686 s | -1.040% | **Fail:** requires at least +10% total and +35% role |
| Yumark HTML | 1.4264 s | 1.4308 s | +0.308% | 15.10 ms | 16.88 ms | +10.545% | Pass: total did not regress |
| repository-std-only | 1.2370 s | 1.2086 s | -2.350% | 8.82 ms | 8.72 ms | -1.147% | **Fail:** 2.350% regression exceeds 2% bound |
| showcase | 1.2070 s | 1.3766 s | +12.320% | 9.10 ms | 9.58 ms | +5.010% | Pass: total did not regress |

Supporting external observations were mean wall time of enabled/always-solve 8.024/7.980 seconds
for Markdown, 1.754/1.740 seconds for HTML, 1.384/1.352 seconds for repository-std-only, and
1.416/1.596 seconds for showcase. Maximum observed RSS in the same mode order was 447,580/447,344
KiB, 218,160/218,228 KiB, 202,480/202,476 KiB, and 205,716/205,884 KiB respectively.

Every enabled release run recorded six exact hits and no cap fallback. Peak loop-local retention
was six entries and 19,764 Debug-proxy bytes, below the 64-entry and 128-MiB caps; always-solve runs
recorded zero hits and zero retained entries. The two Markdown improvement gates and the
repository-std-only control gate therefore reject this activation candidate for release despite
correctness parity and budget compliance. The approved thresholds were not changed after observing
the result.

The completed Slice C investigation is recorded in
`2026-07-16-generalize-role-resolve-snapshot-stage2-slice-c.md`. It found that the six hits above
were only 217.285 microseconds of cheap repeats and that a production-only pending-analysis-queue
guard falsely excluded the expensive Markdown `proof` repeat. Removing that non-input guard made
Markdown pass both approved improvement thresholds, but a ten-pair rerun still failed the
repository-std-only and showcase 2% no-regression gates. Stage 2 production activation therefore
remains held; the preliminary table above must not be used as the final mechanism diagnosis.

### Stage 2 held-default correction (2026-07-16)

The failed final gate is now reflected in the implementation default. New sessions use the
always-full-solve path unless reuse is explicitly selected with
`--generalize-role-snapshot-enable-reuse`. The pre-existing
`--generalize-role-snapshot-always-solve` control keeps the same meaning and is a
default-confirming no-op rather than being repurposed.

A fresh release Markdown run verified 0 hits and 612 full solves for both the bare/default route and
the explicit always-solve route. The new reuse opt-in reproduced 146 hits, 466 full solves, six peak
entries, and 20,653,144 peak Debug-proxy bytes. The full implementation, independent oracle,
telemetry, caps, and corrected false-miss guard are retained for a separately designed
cheap-demand-admission follow-up; reuse is not production-default behavior.

## 9. Diagnostics and telemetry

This is internal scheduling. Cache hits, misses, cap fallback, and shadow disagreement are not source
diagnostics.

Debug/timing telemetry should distinguish:

- full recursive solves;
- exact snapshot hits;
- misses by legacy epoch, supplemental epoch, main, demand, candidate guard, lifecycle, and budget category;
- full-solve and exact-equality time;
- snapshot insert/replace/clear counts;
- current and peak entries and retained bytes;
- result-disposition counts for unresolved, ambiguous, newly resolved, and already applied; and
- shadow resolution-tree, disposition, state-delta, and final-scheme mismatches.

Raw `DefId` and structural detail may appear in debug traces. Correctness and cache eligibility may
not branch on those strings or IDs.

## 10. Rollback and compatibility

Stages 0 and 1 leave the production-selected full-solve path unchanged. Stage 2 was the first
production behavior change, but its final performance gate failed and the production default has
been returned to always-full-solve. The existing always-solve control remains available as a stable,
default-confirming spelling and continuing regression assurance; exact reuse requires the separate
`--generalize-role-snapshot-enable-reuse` opt-in.

One false-reuse counterexample is sufficient for immediate rollback. A false reuse means that an
eligible cache entry returns a recursive resolution result, current-state disposition set, state
delta, or final generalized scheme different from what the unchanged full solver would produce from
the same state.

If one counterexample is found after activation:

1. disable per-demand snapshot hits and restore the unchanged full solve for the affected production
   path;
2. preserve the failing input, exact key values, cached result, full-solve result, and final scheme
   as a regression test;
3. classify whether epoch coverage, main/demand normalization boundary, candidate-table guard,
   applied-state separation, cache lifetime, or result capture caused the false hit;
4. repair the missing exact guard or boundary at its authoritative layer;
5. do not add a fixture/name/path/`DefId` special case and do not redefine the expected full-solver
   result; and
6. do not reactivate production reuse until the complete fixture and adversarial acceptance set
   returns to zero mismatches and the repaired performance gates pass again.

Rollback disables only this loop-local eligibility layer. It must not revert unrelated role-solver,
generalization, owner-scheduling, or final-filter exact-reuse changes.

## 11. Rejected alternatives

1. **Reuse on constraint epoch alone.** The legacy epoch omits four solver-observable mutation
   classes, and iteration inputs also include the post-floor main, normalized demand, and candidate
   table. Legacy epoch equality alone is insufficient.
2. **Use a hash, Debug string, size, or pointer as exact identity.** These can reject work cheaply
   but cannot authorize a correctness-sensitive hit.
3. **Cache the applied disposition or replay old mutations.** Applied membership changes across
   iterations and must be evaluated against current state.
4. **Cache across roots or sessions.** Raw compact structures and candidate/constraint lifecycles
   have no stable cross-root identity in this design.
5. **Treat `ae6afc58`/`cfa017f6` as solver-reuse coverage.** Their final post-loop filtering boundary
   is different from the iteration-3-to-4 solver invocation.
6. **Reuse owner-level dirty-scheduler records.** Their unit, lifetime, and mutation frontier belong
   to forced method-role passes, not generalization.
7. **Skip the whole generalization iteration.** That folds in role/dominance collection reuse and
   requires the separate L-XL/very-high-risk project.
8. **Fix compact-tree ownership as part of cache implementation.** DAG/interning changes the
   representation and is a separate L-XL/high-risk project.
9. **Hard-code the Markdown trace.** The observed names and `DefId`s diagnose the problem but cannot
   define a general inference rule.

## 12. Explicitly deferred and out of scope

### 12.1 Compact tree expansion and DAG/interning

The approximately 95.3x expansion from a shared/deep `cons_cell` shape into an owned
`CompactType` tree is the reason the duplicate solve is expensive. It is not fixed here. Changing
compact values to a DAG, adding global interning, or redesigning ownership is a separate
L-XL/high-risk project with a larger representation and lifecycle proof.

This snapshot may still retain one bounded exact owned value. It may not use the project as cover to
change the compact representation.

### 12.2 Generalization collect-roles/dominance iteration reuse

Avoiding the approximately 330-436 milliseconds of repeated `generalize_collect_roles` and
`generalize_collect_dominance` work per repeat iteration is the separate, not-yet-approved
generalization iteration reuse project. It is L-XL/very-high risk and explicitly excluded from every
stage and completion gate in this document.

### 12.3 Other excluded work

This project also excludes:

- changes to role matching, ambiguity, prerequisite recursion, cycle semantics, or candidate order;
- restart suppression or residual-predicate coalescing;
- constraint replay suppression or evidence changes;
- cross-session/cross-root caching;
- stable global demand identity;
- fixture-, path-, module-, function-, or raw-ID-specific inference behavior; and
- cleanup of the existing final post-loop exact-reuse gates.

## 13. Unconfirmed points and stop conditions

The following are deliberately not guessed:

1. **Candidate guard choice.** Stage 0 decides between a complete generation and mechanically
   enforced root-local immutability. If neither is complete, stop.
2. **Constraint witness completeness (confirmed in Stage 0).** Bare `ConstraintEpoch` is incomplete
   and cannot safely absorb all missing mutations because existing production consumers give it
   control-flow semantics. The selected exact witness is `E` plus the narrow
   `RoleSolveSupplementalEpoch` (`A`). Adding a broad mutation journal remains outside this project
   and requires a size/risk review.
3. **Exact result boundary.** Applied membership must be downstream of the reusable pure result. If
   moving it there requires a semantic solver rewrite, stop before Stage 1.
4. **Storage and comparison cost.** Exact retained values may be large. Entry/byte caps and equality
   costs are TBD until Stage 0; lossy identity is not a fallback.
5. **Numerical activation gates (proposal recorded; approval pending).** Section 8 now records the
   Stage 0/1-measurement-grounded 10% Markdown end-to-end, 35% Markdown role-phase, and 2% per-control
   no-regression proposal. Claude/user confirmation remains required before activation is final.
6. **Breadth of the opportunity.** Stage 0 must find exact repeats across more roots/fixtures than
   the single `proof` witness. If it is fixture-specific, stop rather than add a special case.

If any stage requires candidate-graph polling, a session-wide invalidation journal, compact DAGs,
or reuse of role/dominance prepasses, the project has crossed its M/medium boundary. Stop and report
the expansion instead of silently broadening the design.

## 14. Overall size and risk

Overall estimate: **M, risk medium**.

The project is bounded because snapshots live only within one root's existing generalization loop,
all positive reuse gates are exact, applied membership remains live, and every uncertainty executes
the unchanged solver. The principal work is defining the exact pure-result boundary, enforcing the
candidate guard, retaining bounded exact values, and maintaining an independent shadow comparison.

The medium risk comes from the path's importance rather than broad mutation coverage: a false hit
could silently change a public type scheme, while a false miss is safe. The staged plan therefore
spends two stages with production behavior unchanged and retains the full solver as oracle and
rollback path after activation.

The estimate excludes both representation-level DAG/interning and iteration-wide generalization
reuse. Discovering that either is required triggers the stop condition in Section 13 rather than an
upward revision performed inside implementation.

## 15. Completion gates

The per-demand exact solve snapshot project is complete only when:

- the exact `E/M/D/C/A` input contract is documented and executable;
- candidate-table stability is enforced by a complete generation or immutability mechanism;
- every hit uses structural main/demand equality, never only a hash or identity shortcut;
- the cached result is a complete pure recursive solve result;
- applied membership and state-changing disposition are reevaluated against current state;
- any mismatch, ambiguity, overflow, missing guard, lifecycle escape, or cap failure runs the full
  solver;
- the independent shadow oracle reports zero result/disposition/state/scheme mismatches over all
  focused, adversarial, fixture, and metamorphic tests;
- the representative iteration-4 duplicate no longer invokes the full recursive solver;
- approved wall-time and memory gates pass under controlled release comparison;
- cache state cannot escape one root's generalization lifetime;
- the always-full-solve control and independent oracle remain available;
- one false-reuse counterexample triggers the rollback procedure in Section 10; and
- compact DAG/interning and iteration-wide collect-roles/dominance reuse remain separately scoped.

Design synthesis: Codex (gpt-5.6-sol), 2026-07-16 session, based on the completed read-only
investigation supplied for this task.

Implementation approval is pending Claude/user review. This attribution records the draft
specification only; it is not a Claude signature and does not approve any implementation stage.
