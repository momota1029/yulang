# Owner-level dirty scheduling for method-role resolution

Date: 2026-07-15

Status: draft feasibility and implementation design for Claude/user review. This document is not
Claude-signed, does not approve implementation, and does not amend the role-system or the signed
role-impl lifecycle specifications.

## 1. Purpose

The current method-role pass has two scheduling levels:

1. the `df1c23f3` whole-session guard skips a pass after an exact no-progress snapshot when the
   global constraint epoch, role epoch, and method-role input generation are unchanged; and
2. whenever that guard cannot skip the pass, `resolve_roles_for_unresolved_methods` rebuilds method
   taint and solves every distinct `SelectionUse.parent` from scratch.

The second level is the remaining target. In the measured Yumark Markdown workload, 94 of 95 checks
for the actual render owner were unchanged after its previous no-progress result. Re-running its
main-root compaction, owner-role compaction/coalescing, candidate matching, and transitive
prerequisite search cannot make progress while every value the solve observed remains unchanged.

This follows eight already-landed performance fixes, commits `3fcb9cc1` through `51e9a722`, which
reduced the measured Yumark Markdown cold `build_poly` mean from about 35.7 seconds to 14.36 seconds.
The seventh fix, `df1c23f3`, reduced 190 no-progress method-role passes to 101 and cut measured
method-role-solve cost by 46%. The remaining opportunity is not another local matcher shortcut: it
is the repeated solution of unchanged owners inside the passes which still must run.

The production contract proposed here is:

```text
cached_terminal(owner) = (RootUnavailable | NoProgress, dependency_fingerprint)

all dependencies in dependency_fingerprint are unchanged
  => resolving owner again would return the same terminal outcome
     and would publish no constraint, role resolution, selection, or SCC mutation
```

Only terminal outcomes are reusable. A solve which applies a compact merge constraint or role
resolution is `Progress`; its cache record is discarded, and the ordinary fixed-point lifecycle
continues unchanged.

This project is deliberately limited to owner-level scheduling inside the existing method-role
pass. It does not introduce stable per-demand identities, incremental generalization, early
fallback activation, a cross-session cache, or a shared solver scheduler.

## 2. Verified current state and drift from the initial summary

### 2.1 Current pass lifecycle

`AnalysisSession::drain_work` first drains ordinary work. It then checks
`method_role_pass_inputs_changed`. A proven no-progress snapshot lets it stop before calling
`resolve_roles_for_unresolved_methods`; a progressing or uncertain pass clears the snapshot.

When a pass runs, `resolve_roles_for_unresolved_methods` currently:

1. scans all unresolved selections, sorts and deduplicates their parents;
2. builds one shared `MethodTaintIndex` from all unresolved selections;
3. returns if the index is empty;
4. visits every owner in `DefId` order;
5. obtains `scc.root_of(owner)`;
6. compacts the owner root and raw role constraints, applying any newly discovered merge
   constraints and restarting that owner's local loop;
7. scans visible candidates and recursive prerequisites for the method-tainted demands;
8. applies every new role resolution and routes resulting constraint events; and
9. after the owner loop, re-enqueues unresolved selection probes if any owner progressed.

The whole-session guard remains valuable: when it hits, it avoids the parent scan, method-taint
rebuild, and every owner check. Owner scheduling addresses only passes which the guard must run
because some session input changed.

This also matches the separate early-fallback closeout (`ef85da02` through `48d7b22a`). Activating
candidate-independent wrapper resolution early extended a demand from about five natural late-
fallback rescan rounds to 14-21 rounds. Trigger variants preserved semantic output but regressed
wall time because every forced role pass rebuilt taint and rescanned unchanged owners/candidates.
That project correctly deferred activation instead of treating trigger tuning as invalidation.

### 2.2 Actual shadow-oracle outcome

The test-only oracle does not compare complete solver dispositions. It classifies the real call as:

```text
RootUnavailable
NoProgress
Progress
```

and checks that a predicted-clean owner's classification equals the cached classification.
`Progress` is never cached. `RootUnavailable` and `NoProgress` are cached.

This is the outcome needed for scheduling: both cacheable outcomes have no owner-solve mutation to
replay. It is not evidence that candidate counts, internal dispositions, or timing counters are
identical. Production telemetry must count a cache skip explicitly instead of pretending that the
skipped candidate scans happened.

### 2.3 Owner identity correction

The owner is exactly `SelectionUse.parent`. Under that definition, the root `proof` definition has
no owner checks in either Yumark fixture. The measured 95-check owners are
`render_markdown_doc` and `render_html_doc`. Profiling attribution to `proof` generalization and
method-pass owner identity are related through the workload, but they are not interchangeable.

All observed owner checks in the three-fixture experiment had an SCC root. The oracle therefore has
strong evidence for `NoProgress` reuse and no fixture evidence for repeated `RootUnavailable`
reuse.

## 3. Empirical foundation: the real fingerprint

The oracle starts its per-owner read guard immediately before
`resolve_method_tainted_roles_for_def`. The shared method-taint index has already been built. Read
hooks then record the frontier reached by root compaction, raw-role compaction/coalescing, candidate
compaction, matching, and recursive prerequisite solving.

### 3.1 Top-level owner fields

`OwnerDependencyFingerprint` contains these exact fields:

| Field | Current representation | What it protects |
| --- | --- | --- |
| SCC root | `Option<TypeVar>` | root registration/availability and exact root identity |
| raw owner roles | `RoleEpoch` from `roles.epoch_for_owner(owner)` | addition/change of role constraints owned by this parent |
| owner selections | sorted `Vec<(SelectId, SelectionUse)>` | unresolved membership and every use-site slot/scope field for this owner |
| constraint dependencies | `ConstraintDependencyFingerprint` | compact-observable mutable constraint state actually read |
| candidate buckets | sorted `(role path, test-only bucket epoch)` | every top-level and recursive prerequisite role bucket scanned |
| method-taint projection | sorted `(TypeVar, Option<Vec<SelectId>>)` | only method-taint entries actually queried by short-circuiting taint checks |
| projection selections | sorted `(SelectId, SelectionUse)` | complete use-site data for selections named by the queried taint projection, including other owners |
| applied resolutions | `RoleResolutionKey -> bool` | exact membership results read from `applied_method_role_resolutions` |

The candidate frontier is dynamic and transitive. `role_solve` records the initial demand's role
bucket before candidate lookup and records every rewritten prerequisite role bucket before its
recursive lookup. It does not record per-candidate generations.

### 3.2 Constraint fingerprint

The constraint fingerprint is narrower and more concrete than “the reachable component.” It stores
only variables whose corresponding read API ran:

| Read hook | Fingerprinted value |
| --- | --- |
| `TypeBounds::of(var)` | `Option<ConstraintEpoch>` from that `VarBounds`, not the lower/upper vectors themselves |
| `ConstraintMachine::var_neighbors(var)` | exact sorted neighbor `TypeVar` list |
| `SubtractTable::facts(var)` | exact `Vec<SubtractFact>` |
| `ConstraintMachine::level_of(var)` | exact current `TypeLevel` |
| `ConstraintMachine::birth_level_of(var)` | exact birth `TypeLevel` |
| `ConstraintMachine::pre_pop_effect_families(var)` | exact `Vec<ConstraintEffectFamily>` |

Type-arena nodes are immutable after allocation, so IDs reachable from a recorded bound need no
separate mutation generation. Mutable tables which decide which IDs are reachable do.

### 3.3 Method-taint projection

The oracle does not fingerprint every bounds read used to build `MethodTaintIndex`. Instead, the
current forced pass builds the real index once, and the owner fingerprint records only index entries
which that owner's taint predicates actually query. For each resulting `SelectId`, it also records
the current `SelectionUse`.

This means the proposed owner scheduler can avoid owner solves, but it does not yet avoid the shared
method-taint rebuild. Removing that rebuild would require a separate incremental taint graph and is
not part of this project.

### 3.4 Empirical results

The fresh characterization produced zero clean-prediction mismatches:

| Fixture | Forced passes | Clean owner checks | Actual render owner |
| --- | ---: | ---: | ---: |
| Yumark Markdown | 100 | 7,359 / 7,526 (97.78%) | 94 / 95 (98.95%) for `render_markdown_doc` |
| Yumark HTML | 100 | 7,359 / 7,526 (97.78%) | 94 / 95 (98.95%) for `render_html_doc` |
| repository std only | 91 | 6,317 / 6,480 (97.48%) | not applicable |

Across the three fixtures, 21,035 clean predictions were checked against 21,532 real owner solves.
This is strong empirical evidence that the observed read frontier predicts terminal owner outcomes
for these workloads.

### 3.5 Why the test fingerprint is not yet a production invalidation contract

The zero-mismatch result does not prove that every current mutation changes a value which the
oracle can cheaply notice:

- upper-row pruning removes entries from `VarBounds.uppers` without advancing that variable's
  stored bounds epoch;
- the row-effect `store_upper_bound_without_replay` path can both prune old uppers and insert a new
  upper without recording a new per-variable bounds epoch;
- neighbor additions/removals have no per-variable generation;
- current-level lowering, birth-level registration, subtract facts, and pre-pop families do not
  share one complete per-variable epoch;
- candidate bucket epochs exist only in the test oracle and cover session mutation APIs used by
  real lowering; direct public-table mutation in tests bypasses them;
- owner and projection selection snapshots, exact neighbor/fact/family vectors, and method-taint
  projections are rebuilt and compared by polling; doing that for every owner in production would
  reproduce much of the work this project intends to remove; and
- a zero mismatch compares only the three terminal outcome classes, not exact internal solver
  statistics.

The production project must therefore preserve the oracle's dependency *shape* while replacing
full value polling with a complete, cheap mutation contract.

## 4. Correctness invariant

For a session, let `D(owner)` be the set of mutable resources actually read by the last cacheable
owner solve. A production skip is permitted only when all of these hold:

1. the cached outcome is `RootUnavailable` or `NoProgress`;
2. the owner still has unresolved selection membership consistent with the record;
3. every mutation before the skip has been drained through the scheduler's journal;
4. no resource in `D(owner)` has changed after the record was captured;
5. no unclassified, lost, overflowed, or contract-version-mismatched mutation has occurred; and
6. the record is within the active session and its memory budget.

The scheduler is an optimization of call eligibility only. It may not alter:

- role matching, candidate ordering, prerequisite recursion, or ambiguity rules;
- compact merge generation or application;
- method-taint semantics;
- selection/SCC dependency lifecycles;
- role-resolution keys or the applied-resolution set; or
- ordinary fixed-point and quantification ordering.

A false dirty result costs a redundant solve and is safe. A false clean result can suppress needed
progress and is a correctness bug. Every uncertain state therefore runs the owner, or all owners
when the uncertainty cannot be localized.

## 5. Proposed architecture

### 5.1 Session-owned state

The scheduler lives in `AnalysisSession` and is never serialized:

```rust
struct MethodRoleDirtyScheduler {
    records: FxHashMap<DefId, CachedOwnerTerminal>,
    reverse_subscriptions: FxHashMap<DependencyKey, FxHashSet<DefId>>,
    dirty: FxHashSet<DefId>,
    generations: FxHashMap<DependencyKey, MutationGeneration>,
    drained_mutation_serial: MutationSerial,
    method_taint_snapshot: MethodTaintIndex,
    contract_state: MutationContractState,
    metrics: MethodRoleDirtyMetrics,
}

struct CachedOwnerTerminal {
    outcome: CacheableOwnerOutcome,
    fingerprint: OwnerDependencyFingerprint,
}

struct OwnerDependencyFingerprint {
    dependencies: Vec<DependencyStamp>,
    capture_serial: MutationSerial,
}

struct DependencyStamp {
    key: DependencyKey,
    generation: MutationGeneration,
}
```

Names are illustrative. The semantic requirements are:

- dependencies are deduplicated and stored in deterministic order;
- publishing a new record atomically replaces the owner's old reverse subscriptions;
- starting a progressing/uncertain solve makes its old terminal record ineligible;
- a progressing solve leaves no reusable record;
- a terminal solve records exactly the resources read by that real solve;
- a clean skip returns the cached terminal classification without synthesizing solver work; and
- the existing test-only shadow oracle remains independently runnable, so the production scheduler
  is not validated only against its own recorder.

### 5.2 Dependency vocabulary

The first production version uses these typed keys:

```text
SccRoot(DefId)
OwnerRawRoles(DefId)
OwnerSelections(DefId)
Selection(SelectId)

ConstraintBounds(TypeVar)
ConstraintNeighbors(TypeVar)
ConstraintSubtractFacts(TypeVar)
ConstraintLevel(TypeVar)
ConstraintBirthLevel(TypeVar)
ConstraintPrePopFamilies(TypeVar)

MethodTaint(TypeVar)
CandidateBucket(RolePath)
AppliedResolution(RoleResolutionKey)
```

`OwnerSelections` covers insertion/removal/replacement in the parent's unresolved set.
`Selection` covers the complete use-site values reached through a method-taint projection, which
may name a selection owned by another definition.

A selection insertion/removal/replacement emits `Selection(select)`. It also emits
`OwnerSelections` for the old parent and the new parent when either exists; re-parenting must not
leave the old owner's record subscribed to a set which silently changed. Root registration and
open-component removal emit `SccRoot(owner)`. Raw-role mutation emits `OwnerRawRoles(owner)`, and a
successful first insertion into the applied-resolution set emits `AppliedResolution(key)`.

The six constraint keys mirror the real oracle read hooks. They must be invalidated on value
change, not merely on insertion. In particular:

- pruning/removing an upper emits `ConstraintBounds(source)`;
- an adjacency count transition between absent and present emits `ConstraintNeighbors` for both
  endpoints;
- lowering a current level emits `ConstraintLevel(var)`;
- first registration or changed registration semantics emit the applicable current/birth keys;
- recording a new subtract fact emits `ConstraintSubtractFacts(effect)`; and
- changing the retained pre-pop family vector emits `ConstraintPrePopFamilies(var)`.

Bounds evidence promotion/removal is part of `ConstraintBounds`; it is not a separate hidden lane.

### 5.3 Typed mutation journal and reverse subscriptions

Expanded per-variable epochs alone are not the proposed design. They would still require polling
every dependency stamp for every owner whenever a pass is forced, would need multiple new epochs per
variable, and would not naturally cover candidate buckets, selections, SCC roots, or the global
applied-resolution set.

Instead, authoritative mutators emit:

```rust
enum MethodRoleMutation {
    Changed { serial: MutationSerial, key: DependencyKey },
    InvalidateAll { serial: MutationSerial, reason: InvalidateAllReason },
}
```

The constraint machine owns a small mutation outbox beside its existing constraint-event outbox.
Session-owned role, selection, candidate, SCC, and applied-resolution mutators write to the session
journal. Infer-local wrappers or low-level table generations must cover direct mutation APIs; a
contract which exists only in `register_role_impl_candidate` while raw table mutation remains
silently possible is not complete.

At synchronization, changed keys are deduplicated, their generations advance, and subscribed
owners become dirty. The reverse index distributes each mutation once; it avoids reconstructing
the old exact value snapshot for every owner. A record may retain generation stamps for assertions
and recovery, but a normal clean check is allowed only after the journal is fully drained.

Mutation generation uses checked increment. Overflow, a truncated journal, an unknown key kind, a
mutation-contract version mismatch, or an audit-fence mismatch emits `InvalidateAll`. Saturating an
epoch and continuing to call owners clean is forbidden.

### 5.4 Capturing reads without a production-wide thread-local hot path

The test oracle uses thread-local hooks because it is `#[cfg(test)]`. The production design should
not turn every constraint read in every compiler phase into a thread-local lookup.

The proposed split is:

1. `ConstraintMachine` owns an inactive-by-default, session-local owner-read collector. The six
   compact-observable read APIs append typed keys only while an owner solve has activated it.
2. Owner-role, candidate-bucket, applied-resolution, and method-taint reads receive the same
   crate-private collector through the method-role solve call chain.
3. `AnalysisSession` adds root and owner-selection dependencies at orchestration boundaries and
   adds `Selection(select)` for every select returned by a queried taint projection.
4. Beginning a second collector while one is active is an invariant violation; finishing or
   unwinding always clears it.

This keeps the recorder scoped to the real solve and avoids CST/constraint rescans. Stage 1 may
adjust the exact borrowing/API shape, but may not fall back to polling the complete fingerprint
before each owner or to always-on TLS in release builds without measured approval.

### 5.5 Method-taint handling

The existing shared index is rebuilt once whenever the whole-session guard admits a pass. The
scheduler retains the previous index and computes a deterministic diff over `(TypeVar,
sorted SelectId list)`. A changed entry emits `MethodTaint(var)` before owner eligibility is tested.

Selection mutations already advance the coarse method-role contract generation, so the top-level
guard cannot hide a needed taint rebuild. The diff turns the derived index into typed invalidation
without asking every owner to reconstruct its old projection.

This design intentionally leaves the rebuild cost in place. If it becomes dominant after owner
activation, incremental method taint is a separately scoped project.

### 5.6 Candidate and prerequisite invalidation

The initial candidate unit is a role bucket, not one candidate. Current solving scans every
candidate in `impls.candidates(role)`, so any insertion or relevant mutation within that bucket can
change the result.

Registration emits `CandidateBucket(candidate.role)`. Extending prerequisites for `impl_def` emits
the bucket key for every candidate belonging to that impl. An infer-local `impl_def -> role bucket`
index should make this lookup direct rather than rescanning the whole candidate table.

Reverse transitive prerequisite invalidation needs no static prerequisite graph. The real solve
records every prerequisite bucket it recursively reads. A later mutation to any such bucket dirties
the subscribed owner directly. Changing candidate A's prerequisite list dirties A's own bucket;
changing candidates in prerequisite bucket B dirties every owner whose previous solve actually
reached B.

Per-candidate generations are deferred. They would be finer than the current scan unit and would
require proving which candidate fields a failed precheck did not observe.

### 5.7 Pass composition and ordering

The two scheduling levels compose as follows:

```text
drain ordinary work
  -> unchanged whole-session snapshot?
       yes: stop; no parent scan, taint rebuild, or owner check
       no:
         begin method-role pass
         collect current owners
         build and diff method taint
         drain mutation journal
         for owner in current deterministic order:
           drain mutation journal
           if terminal record exists and owner is clean:
             record skip; reuse terminal classification
           else:
             run the unchanged real owner solve with read capture
             drain mutations produced by the solve
             cache only RootUnavailable/NoProgress
         preserve existing progress routing and selection reprobes
```

Journal synchronization before each eligibility decision is required. An earlier owner may apply a
resolution which changes a later owner's dependency; that later owner must run in the same pass.
Likewise, a later owner may change a dependency of an owner already visited; the reverse
subscription leaves the earlier owner dirty for the next fixed-point pass. Current owner order and
the rule that each owner runs at most once per pass remain unchanged.

### 5.8 Composition with the whole-session guard

The `df1c23f3` guard remains as the top-level fast path. Its snapshot must incorporate the coarse
mutation-contract generation, or every relevant typed mutation must advance the existing
`method_role_input_generation`. The former is easier to audit explicitly.

The existing constraint/role/input fields remain during initial activation. They are conservative
and already tested. Removing them as redundant would be a later cleanup decision after the new
contract has independent evidence; it is not part of this project.

### 5.9 Cache lifetime and budget

Records are session-scoped. They are removed when:

- an owner has no unresolved selections;
- its component settles/quantifies or its root lifecycle becomes terminal;
- a new solve progresses;
- the record is replaced after a new no-progress solve;
- an `InvalidateAll` condition occurs; or
- a configured owner/dependency/reverse-edge memory cap is exceeded.

Resolved selections and settled SCCs must not leave reverse-subscription tombstones. Per-owner cap
overflow makes that owner non-cacheable. A global reverse-index or journal cap disables all owner
skips and runs the full existing pass until a fresh bounded state can be established.

Absolute caps are not guessed in this document. Stage 5 measures live owners, dependency keys,
reverse edges, journal bursts, and retained bytes, then proposes constants for explicit approval
before activation.

### 5.10 Failure policy

Recognized mutations invalidate only subscribed owners. Unrecognized or unlocalizable mutations
invalidate the complete owner cache and force every current owner through the unchanged solver.

This distinction is mandatory. An “unknown mutation” cannot safely choose one owner. It also cannot
be ignored because the whole-session guard happened to advance. Unknown fallback is a performance
loss, never a source diagnostic or type fallback.

## 6. Explicit resolutions of the ten decision points

These are proposed resolutions for review, not signed decisions.

### 6.1 Decision 1: project boundary

**Proposed resolution (2026-07-15): limit version 1 to the method-role pass.**

The dependency vocabulary may use reusable internal types, but proof generalization and early
fallback are not consumers or acceptance criteria. This preserves the smallest empirically
justified slice and prevents a scheduler project from becoming a shared inference lifecycle
rewrite.

### 6.2 Decision 2: payoff gate

**Proposed resolution (2026-07-15): require both correctness and time-weighted payoff; clean count
alone is insufficient.**

Proceed beyond Stage 0's shadow-oracle-style measurement only if:

1. every predicted-clean owner has zero terminal-outcome mismatches over the acceptance set;
2. each Yumark fixture and repository-std-only remains at least 90% clean among root-available
   owner checks; and
3. owners predicted clean account for at least 50% of measured owner-solve time in each Yumark
   fixture, not merely 50% of calls.

Production activation additionally requires, over five alternating release rounds:

- at least 50% lower `method_role_solve` mean;
- at least 30% lower complete method-role-pass mean including method-taint rebuild;
- at least 5% lower Yumark Markdown cold `build_poly` mean; and
- no greater than 2% mean regression on Yumark HTML, repository-std-only, or the representative
  std/showcase control after noise is characterized.

These thresholds are intentionally proposed for human review. Failure stops activation; it does not
justify weakening invalidation or widening scope.

### 6.3 Decision 3: initial scheduling unit

**Proposed resolution (2026-07-15): owner-only.**

`SelectionUse.parent` is already the orchestration unit, the oracle evidence is owner-based, and an
owner solve has a clear terminal result. Stable coalesced-demand identity would require tracking
demand split/merge topology and is a separate L/high project.

### 6.4 Decision 4: invalidation contract

**Proposed resolution (2026-07-15): typed mutation journal plus reverse-dependency subscriptions,
with a coarse fail-closed audit fence.**

The compact-observable state is exactly the dependency vocabulary in Section 5.2. Expanded bounds
epochs alone are rejected because they neither cover the other tables nor avoid per-owner polling.
Every authoritative mutator must emit a typed event or `InvalidateAll`.

### 6.5 Decision 5: candidate granularity

**Proposed resolution (2026-07-15): per-role-bucket generations in version 1.**

The solver scans a whole role bucket, so the bucket is the proven invalidation unit. Recursive
prerequisite buckets are captured dynamically. Per-candidate generations and a static reverse
transitive prerequisite graph are deferred until bucket invalidation is measured as a material
source of false dirty work.

### 6.6 Decision 6: cache lifetime and memory budget

**Proposed resolution (2026-07-15): session-only, eager stale-record removal, and fail-closed hard
caps selected from Stage 5 measurements.**

No record crosses quantification, session finish, or artifact boundaries. Per-owner overflow makes
only that owner non-cacheable; global journal/reverse-index overflow disables all skips. Exact caps
remain an explicit pre-activation human decision.

### 6.7 Decision 7: failure policy

**Proposed resolution (2026-07-15): every unrecognized mutation forces a full current-owner pass.**

Localized recognized mutations dirty only subscribed owners. Unknown provenance has no sound owner
projection, so full-session method-role invalidation is the smallest safe response.

### 6.8 Decision 8: early-fallback scope

**Proposed resolution (2026-07-15): keep this project independent of early-fallback production
activation.**

The 2026-07-14 project remains a required regression/acceptance workload because it exposed the
scheduling cost, but making its seven helped methods run early is not a completion gate. After this
project is stable, early fallback can be re-profiled and separately approved.

### 6.9 Decision 9: generalization scope

**Proposed resolution (2026-07-15): reuse `ae6afc58`/`cfa017f6` final-role-solve snapshots as-is and
do not schedule intermediate generalization iterations here.**

Intermediate `generalize_collect_roles`/`generalize_collect_dominance` reuse needs a different
reachability and mutation frontier. Folding it into this owner scheduler would erase the clear
method-pass correctness boundary.

### 6.10 Decision 10: benchmark acceptance set

**Proposed resolution (2026-07-15): the Yumark pair is necessary but not sufficient.**

Correctness and payoff evidence must include:

- Yumark Markdown and HTML;
- repository std only;
- `check-poly-std examples/showcase.yu` or its current equivalent;
- the 2026-07-14 early-fallback project's wrapper/`ParseError.merge` cases;
- focused adversaries for every dependency key and `InvalidateAll`; and
- ordinary non-role and small role fixtures to detect fixed overhead.

The full infer test suite remains the semantic regression set. Wall-clock activation thresholds use
release builds and explicit route/counter checks rather than CI timing assertions.

## 7. Rejected alternatives

1. **Poll the current shadow fingerprint before every owner.** Exact vector and projection rebuilds
   would repeat reachable-component work and erase much of the gain.
2. **Use only the global `df1c23f3` generation.** It proves a whole pass unchanged but cannot tell
   which owner changed when the pass is forced.
3. **Add one per-variable epoch.** Bounds, pruning, neighbors, levels, subtract facts, and pre-pop
   families have different mutation lifecycles; selections, candidates, roots, and applied keys are
   not per-variable state.
4. **Use one global candidate epoch.** Any new candidate would dirty every owner, losing the role-
   bucket locality measured by the oracle.
5. **Start with per-candidate or stable demand identity.** It is finer than the current scan unit
   and requires new split/merge/prerequisite identity proofs before owner scheduling has been tried.
6. **Cache progress or replay resolutions.** Progress mutates constraints and selection/SCC work;
   replay would be a semantic incremental solver, not scheduling.
7. **Remove the whole-session guard.** It remains the cheapest path when absolutely nothing changed.
8. **Share the scheduler immediately with generalization and early fallback.** Their roots,
   outcomes, and lifecycle invalidation differ and would raise the project to L-XL/very-high.
9. **Trust fixture success as a complete mutation proof.** The current pruning epoch gap is a
   concrete counterexample to that inference even though it caused no observed mismatch.
10. **Cache across sessions or compiled artifacts.** Raw `DefId`, `TypeVar`, and constraint-node
    identities are session-local and no stable dependency identity is designed here.

## 8. Staged implementation plan

Sizes use the repository's `S / M / M-L / L / L-XL` review scale. Risk uses
`low / medium / medium-high / high / very-high`.

No stage may begin merely because it appears below. This draft first needs Claude/user review.
“Decision-free” means characterization/scaffolding can proceed after the design is accepted without
a new semantic judgment; it does not override the pending approval at the end of this document.

### Stage 0: time-weighted characterization and drift lock

- Size: S.
- Risk: low.
- Approval class: decision-free characterization.
- Changes: extend the existing test-only oracle with per-owner solve duration, cacheable outcome
  counts, root-unavailable counts, dependency cardinalities, and method-taint versus owner-solve
  timing. Add focused witnesses for the current upper-pruning and row-effect no-replay epoch gaps.
  No production behavior.
- Exit criteria:
  1. the 100/100/91 forced-pass and clean-rate characterization is reproduced or any drift is
     explained;
  2. `proof` versus render-owner identity remains explicit;
  3. time-weighted avoidable work is measured separately from call count;
  4. every actual fingerprint field/read hook is covered by an inventory test;
  5. the pre-implementation continuation criteria in Section 6.2 items 1-3 pass, or the project
     stops before Stage 1.

### Stage 1: dependency vocabulary and mutation-contract harness

- Size: M.
- Risk: medium.
- Approval class: decision-free scaffolding, test-only/inactive.
- Changes: define typed dependency/mutation test views, a deterministic contract matrix, journal
  overflow/unknown outcomes, and mutation adversaries. Prototype the session-local read collector
  without making skip decisions.
- Exit criteria:
  1. every real oracle read maps to one typed dependency key;
  2. bounds add/evidence/prune, neighbor add/remove, level/birth, subtract, and pre-pop mutations
     each have an expected event;
  3. selection, raw-role, root, candidate/prerequisite, taint, and applied-membership cases are
     represented;
  4. an unrepresented mutation produces `InvalidateAll`, never silence;
  5. the recorder has no always-on release TLS design and no full-fingerprint polling path.

### Stage 2: complete production mutation journal

- Size: M-L.
- Risk: medium-high.
- Approval class: explicit human sign-off before implementation.
- Changes: add authoritative mutation outboxes/generations to the constraint machine and
  session-owned tables/wrappers; add candidate `impl_def -> role bucket` indexing; extend the
  whole-session snapshot with the coarse contract generation. Do not skip owners.
- Exit criteria:
  1. every effective compact-observable mutation emits the correct key or `InvalidateAll`;
  2. no-op/deduplicated mutations may conservatively dirty but may not silently change state;
  3. direct production mutation APIs cannot bypass the contract;
  4. pruning/removal and adjacency transition tests pass even when old bounds epochs would not
     detect them;
  5. overflow and audit-fence disagreement clear all eligibility;
  6. production output is unchanged and disabled-journal overhead is measured.

#### Stage 2 first attempt (2026-07-15): correctness passed, performance gate failed

A first implementation attempt wired real mutation emission into all identified production sites
(constraint-machine bounds/neighbors/levels, the two known epoch gaps, session-owned role/selection
wrappers, and a candidate `impl_def -> role bucket` index). Correctness verification was clean:
`cargo check`/`cargo test -p infer --lib` showed zero regressions beyond the 5 known-unrelated
Yumark DefId-ordering failures, and a repository-std semantic comparison (`dump-poly-std
examples/showcase.yu`) produced an identical SHA-256 hash before and after.

However, the "disabled-journal overhead" measurement (exit criterion 6) failed: 5 timing samples of
the Yumark Markdown cold-compile workload averaged 15.958s, roughly 11% above the ~14.36s baseline
established earlier this session and outside normal measurement noise. The likely cause: the session
mutation outbox is not yet drained or bounded by any consumer (Stage 3 does not exist yet), so every
low-level constraint mutation (bounds, neighbors, levels -- occurring hundreds of thousands of times
per compile per this session's own profiling data) accumulates in an ever-growing record for the
entire session lifetime. "Record everything, unconditionally, for later consumption" is not free at
this mutation volume.

A separate, independent architectural finding surfaced during verification: the first attempt defined
the mutation vocabulary types in `analysis::session` and had `crates/infer/src/constraints/mod.rs`
import them, making the low-level `constraints` module depend on the higher-level `analysis` module.
This does not match this codebase's existing precedent, where constraint-machine-local instrumentation
types (`ConstraintTiming`, `ReplayFrontierShadow`, `ConstraintEvent`) are defined inside `constraints`
itself, with `analysis` depending on `constraints` and not the reverse. A corrected version relocating
the mutation vocabulary into a new `constraints::mutation` module (dependency direction:
`analysis`/`roles` -> `constraints::mutation`) was drafted but not verified against the performance
gate before the whole attempt was set aside.

Both the failed commit and the uncommitted layering fix were discarded; the repository was reset to
Stage 1 (`9e8e583e`), which remains the last verified-good state. Nothing from this attempt landed on
`main`. The stashed work (`git stash`, message "WIP: Stage 2 layering fix attempt (journal design
still fails overhead gate)") is preserved locally for reference but is not assumed correct or reusable
without re-verification.

Design implication for a revised Stage 2: an always-on, unbounded, unconsumed mutation log is not
viable at this mutation volume. A revised approach must do one of: (a) bound/summarize the outbox
(e.g., coalesce repeated mutations to the same key rather than retaining a full history, or represent
"changed since serial N" more cheaply than an append-only log), (b) merge Stage 2 and Stage 3 so the
journal is drained by a real consumer as it's produced rather than accumulating indefinitely, or (c)
gate journal emission behind a session-lifetime activation flag that a later stage can enable only
when the whole-session guard has already determined a pass will be forced (deferring the cost to
exactly the cases where it could pay off). This decision needs human judgment before any second Stage
2 attempt begins; it is not something to guess at silently. The corrected module-layering direction
(`constraints::mutation` owned by the low-level module) should be preserved in the next attempt
regardless of which outbox-design option is chosen.

#### Stage 2 second attempt (2026-07-15): activation-gated design verified

Following the first attempt's performance-gate failure, the user selected remedy (c): gate all
mutation-journal emission behind a session-lifetime activation flag, enabled only immediately before
a forced method-role pass runs (right when the whole-session `df1c23f3` guard determines a pass
cannot be skipped) and disabled again immediately after. The mutation vocabulary was also relocated
into a new `crates/infer/src/constraints/mutation.rs` module, correcting the first attempt's layering
violation: `constraints::mutation` is now self-contained, and `analysis`/`roles` depend on it, not the
reverse.

Verification: `cargo check -p infer` compiled cleanly with zero warnings. `cargo test -p infer --lib`
showed 776 passed / 5 known-unrelated Yumark DefId-ordering failures (baseline after Stage 1 was 767
passed / 5 known failures -- 9 new activation-aware tests added, zero regressions). A repository-std
semantic comparison (`dump-poly-std examples/showcase.yu` SHA-256) was byte-identical before and
after. New tests confirm mutation emission is a complete no-op when the journal is inactive and
produces the correct typed key when active, for both constraint-machine mutators (bounds, neighbors,
evidence) and session-level mutators (selection/role/candidate registration).

The overhead measurement initially looked ambiguous: absolute timing against the session's original
~14.36-15.5s baseline showed the gated build running at ~15.1-15.9s across several rounds, a
seeming regression. However, a controlled analysis resolved this: (a) a same-time A/B comparison
between the gated build and a temporarily-disabled-journal build showed no consistent difference
(gated was measured slightly faster in more than one comparison), and (b) a same-environment,
same-timeframe comparison between the final commit (`c77ef953`) and the pre-Stage-2 baseline commit
(`9e8e583e`), built and measured back-to-back just now, showed the gated Stage 2 build running about
4.8% FASTER than the Stage 1 baseline, not slower. The conclusion: the original ~14.36-15.5s absolute
baseline had become stale after many hours of continuous heavy compilation in this session's shared
environment (thermal/load drift), not because of any real overhead in this design. Absolute wall-clock
baselines established early in a very long working session should not be trusted for later go/no-go
decisions in the same session without a fresh same-environment control measurement; same-time A/B
comparisons are the reliable signal.

An operational hazard was also confirmed during this stage: a Codex MCP call that times out on the
client side (this session hit six ~30-minute timeouts total) does not necessarily stop running on the
server side. On at least three occasions this session, a timed-out call's underlying process continued
executing and eventually committed its own work to the local repository without ever returning a
response to the client -- including once, during this stage, while a SEPARATE, independently-launched
verification call was simultaneously reading/measuring the same working tree, which the verifier
correctly flagged as a mid-verification provenance concern. Practical mitigation used this session:
always re-check `git log`/`git status`/`git diff --stat` immediately after any timeout before assuming
nothing happened, and re-verify a commit's actual content independently rather than trusting a
verification report generated against a working tree that may have changed underneath it.

Commit `c77ef953` (`perf(infer): gate method-role mutation journal`) is pushed. Stage 2 is complete.

### Stage 3: journal-backed owner scheduler in shadow mode

- Size: M.
- Risk: medium-high.
- Approval class: explicit human sign-off before implementation.
- Changes: add session records, reverse subscriptions, method-taint diffing, owner read capture,
  stale-owner cleanup, and dirty predictions. Continue to run every real owner solve and compare
  terminal outcomes against both the new scheduler and the independent shadow oracle.
- Exit criteria:
  1. zero predicted-clean terminal mismatches over the complete acceptance set;
  2. journal-backed and exact-snapshot clean/dirty predictions agree, or every conservative extra
     dirty is explained;
  3. same-pass earlier/later owner mutation order has focused witnesses;
  4. record replacement removes old reverse subscriptions;
  5. resolved/quantified owners leave no tombstones;
  6. Section 6.2 correctness and payoff gates still pass.

### Stage 4: test-only real skipping and semantic parity

- Size: M.
- Risk: high.
- Approval class: explicit human sign-off before implementation.
- Changes: permit owner skips only under tests/explicit benchmark mode; run paired always-solve and
  scheduled sessions; add adversaries for every dependency and fallback path.
- Exit criteria:
  1. finalized schemes, role candidates, selections, SCC outcomes, diagnostics, and runtime/lowered
     outputs match the always-solve baseline;
  2. every mutation-key adversary wakes the affected owner;
  3. an unrelated mutation leaves an independently subscribed owner clean;
  4. unknown mutation, journal loss, cap overflow, and generation overflow run all owners;
  5. the early-fallback fixtures retain their current production behavior and census;
  6. no owner runs more than once per pass and no cached progress is replayed.

### Stage 5: production-shaped disabled benchmark and budget selection

- Size: S-M.
- Risk: medium-high.
- Approval class: explicit human sign-off before implementation.
- Changes: compile the scheduler in release builds behind an off-by-default benchmark/shadow
  switch; measure skip cost, method-taint cost, owner solve time, journal bursts, dependency memory,
  reverse edges, and full cold timings. Production route remains always-solve.
- Exit criteria:
  1. all Section 6.2 activation performance gates pass;
  2. fixed overhead on non-role/small fixtures is within the accepted noise budget;
  3. absolute owner/dependency/reverse-edge/journal caps are proposed from measurements and approved;
  4. no benchmark mode can silently become the default route;
  5. route counters distinguish whole-pass skip, clean-owner skip, dirty solve, and full fallback.

#### Stage 5 first attempt (2026-07-15/16): real correctness gap found, tree reset

A first implementation attempt added an off-by-default CLI benchmark flag
(`GlobalOptions.owner_dirty_scheduler_benchmark: bool`, defaulting to `false`) and promoted the Stage
3/4 scheduler from `#[cfg(test)]`-only toward real release-build code. Verification found a real
correctness gap before any performance measurement was attempted: the production-side
constraint-dependency read hooks (the ones capturing `ConstraintBounds`/`ConstraintNeighbors`/
`ConstraintSubtractFacts`/`ConstraintLevel`/`ConstraintBirthLevel`/`ConstraintPrePopFamilies` reads)
remained `#[cfg(test)]`-gated even though the scheduler itself was being promoted to run in release
builds under the new flag. This means enabling the benchmark flag in a release build would have
produced a scheduler that could not observe constraint-level mutations at all, risking false-clean
predictions in benchmark mode -- a real soundness gap, not a performance question. Unused-import and
unused-constructor compiler warnings in the verification snapshot were direct evidence: the production
capture entry points existed but were never called.

A second issue surfaced during the same verification: the working tree was mutated by an unmanaged,
still-apparently-running background process while verification was in progress (the diff grew across
multiple re-checks, eventually including files well outside this stage's intended scope, such as an
unrelated formatting diff in `crates/evidence-vm/src/runtime.rs`). This made it impossible to trust
that any single compile/test snapshot corresponded to a fixed, reviewable diff. The entire attempt
(both the correctness gap and the unstable tree) was discarded via `git stash` and a hard reset to
`e959c96c` (Stage 4's last verified-good, pushed state); a small amount of orphaned debris that
continued to appear afterward (a stray generic-parameter reference in a test file with no
corresponding production change) was separately discarded via `git checkout --`. Nothing from this
attempt landed on `main`.

Design implication for the next Stage 5 attempt: production-promote the constraint-level read hooks
(currently `#[cfg(test)]`-gated since Stage 0) alongside the scheduler itself, gated behind the SAME
off-by-default benchmark flag rather than left permanently test-only -- the flag should activate the
whole observation chain (constraint reads, session-level mutators, and the scheduler's prediction
logic) as one unit, not the scheduler alone. Before starting a second attempt, explicitly confirm no
other Codex session is still executing in the background (re-check `git log`/`git status` partway
through any long-running verification, not just at the start and end) -- this project has now observed
unmanaged concurrent tree writes on multiple separate occasions this session (Stage 2's first attempt,
Stage 3, Stage 4, and this Stage 5 attempt), and Stage 5 in particular showed a writer still active
well after the client-side timeout that originally triggered recovery, and even after an initial
`git reset --hard`.

#### Stage 5 second attempt (2026-07-16): correctness gap fixed, activation gates pass

A corrected attempt promoted the production-side constraint-dependency read hooks alongside the
scheduler under the same off-by-default benchmark flag (`--owner-dirty-scheduler-benchmark`,
`GlobalOptions.owner_dirty_scheduler_benchmark: bool`, defaulting to `false`), fixing the gap found in
the first attempt. A new non-test `record_owner_dependency_read` collector now captures all six
constraint-level dependency kinds (`ConstraintBounds`/`ConstraintNeighbors`/`ConstraintSubtractFacts`/
`ConstraintLevel`/`ConstraintBirthLevel`/`ConstraintPrePopFamilies`) from real production read sites,
reachable end-to-end when the benchmark flag is enabled, while remaining a complete no-op when it is
not. Verification confirmed the previously-telltale unused-import/unused-constructor compiler warnings
are gone -- direct evidence the hooks are now genuinely wired rather than merely defined.

Verification (independent, maximally skeptical, with the tree checked for stability at multiple points
throughout -- no unmanaged concurrent writes were observed this time): `cargo check -p infer`/
`-p yulang` compiled cleanly with zero warnings; `cargo test -p infer --lib` showed 798 passed / 5
known-unrelated Yumark DefId-ordering failures (baseline after Stage 4 was 795 passed / 5 known
failures -- 3 new tests, zero regressions); a release build succeeded; the default (flag-off) path
produced a byte-identical SHA-256 to a fresh same-time rebuild of the last known-good commit; and,
notably, running WITH the benchmark flag enabled produced byte-identical compiled output to the
flag-off path as well, confirming the scheduler changes scheduling only, never semantics.

Section 6.2's activation performance gates were measured on real release builds (5 alternating pairs
each) and all passed, several by a wide margin: Markdown `method_role_solve` mean dropped 72.14%
(gate: >=50%); complete method-role-pass mean (including taint rebuild) dropped 63.53% (gate: >=30%);
Markdown cold `build_poly` mean dropped 8.08% (gate: >=5%); HTML, repository-std-only, and showcase
`build_poly` means dropped 20.37%, 18.83%, and 15.37% respectively -- all improvements, not the
regressions the gate merely required staying under 2% of.

Route counters for the Markdown fixture: 89 whole-pass skips, 7,359 clean-owner skips, 167 dirty
solves, 0 full fallbacks (no `InvalidateAll` conditions were hit in these fixtures).

Peak resource usage was measured across all four representative fixtures (Markdown/HTML/
repository-std-only/showcase) to inform absolute cap selection, per spec Section 5.9's requirement
that these come from real measurement:

| Workload | Owners | Dependency keys | Per-owner deps (max) | Reverse edges | Journal burst (max) | Retained bytes (approx) |
|---|---:|---:|---:|---:|---:|---:|
| Markdown | 78 | 26,811 | 213 | 2,884 | 60,424 | 5,495,913 |
| HTML | 78 | 26,822 | 213 | 2,884 | 60,424 | 5,503,170 |
| Repository std-only | 74 | 23,878 | 213 | 2,812 | 60,424 | 5,487,738 |
| Showcase | 79 | 25,210 | 213 | 2,860 | 62,163 | 5,509,277 |

No absolute caps are enforced yet -- all cap fields remain unset (`None`) pending explicit human
approval per spec Section 5.9. This is the one open item before Stage 5 can be considered fully
closed; Stage 6 (default production activation) should not begin until caps are approved and wired.

### Stage 6: fail-closed production activation

- Size: S-M.
- Risk: high.
- Approval class: separate explicit human sign-off immediately before activation.
- Changes: enable clean terminal owner skips by default inside forced method-role passes. Retain the
  whole-session guard, exact owner order, independent debug oracle, and all full-pass fallbacks.
- Exit criteria:
  1. Yumark Markdown/HTML and repository std meet the approved correctness/performance gates;
  2. showcase and ordinary controls have no accepted regression;
  3. unknown/capped/overflowed states demonstrably execute the full existing owner loop;
  4. production output and structured diagnostics match the always-solve mode;
  5. method-taint rebuild remains once per forced pass, not once per owner;
  6. no source path/name/fixture condition influences scheduling.

#### Stage 6 complete (2026-07-16): gate shortfall found and fixed, default activation verified

A first Stage 6 attempt flipped the scheduler's activation to default-on and was fully correctness-verified
(zero divergence across the complete 8-item acceptance set: Markdown, HTML, repository-std-only,
showcase, early-fallback census, rename/module-move, ordinary non-role, small-role; all fail-closed
adversarial tests for unknown-mutation/cap-overflow/journal-overflow passed) but fell short of the
required >=5% Yumark Markdown `build_poly` improvement, measuring only 3.14% even though the
mechanism's own targeted metric (`method_role_solve`) improved 73.92% and HTML/repository-std-only/
showcase all comfortably exceeded 5% (11-19% each).

A follow-up investigation (working from a temporarily-applied stash, tree restored to clean and stash
preserved afterward) found the precise root cause: once the first forced method-role pass activated
the mutation journal, journal recording stayed active for the rest of the session -- a one-way latch
inherited from Stage 3's original test-only-scheduler design (where persisting activation across
passes was necessary to avoid collapsing the clean-prediction rate, per Stage 3's own history) but now
costly since Stage 6 makes this the always-on default. Every ordinary constraint mutation throughout
the rest of compilation kept getting recorded even outside method-role passes. Measured impact: the
`analysis.route` phase went from 5.4ms (always-solve) to 105.9ms (scheduler-on), a +100.5ms cost
almost exactly matching the ~98.66ms shortfall against the 5% gate. A duplicate mutation-outbox
synchronization in the routing path (`route_constraint_events` calling `sync_method_role_mutation_outboxes`
both directly and transitively through `owner_dirty_scheduler_drain_journal`) compounded this. The
investigation calculated a "mechanism-adjusted ceiling" of ~6.06% if the overhead were eliminated --
comfortably above the 5% gate, confirming this was a fixable implementation cost, not an inherent
arithmetic ceiling from Markdown's already-small post-optimization method-role share (~10.89% of total
`build_poly`, down from a much larger share before this session's earlier fixes).

The fix (built on the stashed first attempt, applied via `git diff | git apply` since `.git stash apply`
itself hit the same read-only-filesystem sandbox constraint seen throughout this session): make journal
emission subscription-aware rather than session-wide-always-on -- only `DependencyKey`s with a live
reverse-subscription from some owner get recorded, while cross-pass persistence (required since Stage 3)
is unchanged; the recording criterion changed (WHICH keys), not the activation window (WHEN). The
duplicate synchronization was also removed. This deliberately avoided reintroducing Stage 3's original
problem: Markdown's clean-owner-skip rate was re-confirmed at ~97.78% (not collapsed to the ~3.59% a
naive "only record during an active pass" policy had caused when first tried in Stage 3).

Full re-verification after the fix: zero divergence across the complete acceptance set (unchanged from
the first attempt); Stage 3's clean-rate concern confirmed absent; `cargo test -p infer --lib` showed
809 passed / 5 known-unrelated failures (2 new tests, zero regressions); fresh Section 6.2 gate
measurements (same-time A/B against `aa4033b8`) all passed: Markdown `build_poly` -5.799% (gate: >=5%),
HTML -23.35%, repository-std-only -25.65%, showcase -23.35% (all comfortably under the <=2%-regression
gate that only ever required non-Markdown fixtures not to get worse); repository-std semantic SHA-256
was byte-identical before and after. Commit `72467f78` (`perf(infer): activate subscription-aware owner
scheduling by default`) is pushed.

**Owner-level dirty scheduling is now active by default in production** -- the `--owner-dirty-scheduler-
benchmark` CLI flag from Stage 5 remains a compatible no-op (kept rather than removed, per Stage 5's
own deferral of that decision to Stage 7's cleanup). Only Stage 7 (hardening, cleanup, and project
closeout) remains.

### Stage 7: hardening, cleanup, and project closeout

- Size: S-M.
- Risk: medium-high.
- Approval class: explicit human sign-off after Stage 6 evidence.
- Changes: remove only demonstrably duplicate instrumentation, retain an independent regression
  oracle, finalize metrics/caps/docs, and record whether a separate project should revisit method
  taint, early fallback, finer candidate identity, or generalization.
- Exit criteria:
  1. the whole-session guard remains unless separately reviewed;
  2. the independent always-solve comparison remains available in tests;
  3. no stale scheduler state survives session finish or owner settlement;
  4. project notes distinguish realized wall-time gain from clean-call percentage;
  5. any early-fallback/generalization reuse proposal is scoped separately rather than activated
     as cleanup.

## 9. Acceptance oracles

### Oracle D0: independent terminal-outcome shadow

For every predicted-clean owner, run the unchanged solve and compare
`RootUnavailable/NoProgress/Progress`. The existing exact-snapshot oracle and the journal-backed
prediction must be independently available through Stage 6.

### Oracle D1: mutation-contract matrix

Each dependency key has positive and negative tests. Positive tests change the observed value and
must dirty the owner. Negative tests mutate an unrelated key and must not dirty it. Removal/pruning,
absence-to-presence, and presence-to-absence transitions are mandatory.

### Oracle D2: candidate prerequisite transitivity

One owner reads role bucket A, candidate A reaches prerequisite buckets B and C, and another owner
does not. Mutating A, B, or C dirties the first owner. Mutating an unread bucket D does not. Changing
A's prerequisite list also dirties A's readers.

### Oracle D3: method-taint projection and cross-owner selection

Changing the taint list for a queried variable dirties the reader. Keeping the list but changing a
referenced selection use-site also dirties it. Changing an unqueried taint entry does not. Short-
circuit query behavior is covered so a disappeared earlier taint wakes the owner before later vars
become relevant.

### Oracle D4: pass-order mutation

An earlier owner changes a later owner's dependency, and the later owner runs in the same pass. A
later owner changes an earlier owner's dependency, and the earlier owner runs in the next pass.
Neither case reorders owners or runs one twice in a pass.

### Oracle D5: fail-closed contract failure

Unknown mutation, missing journal entry, contract-version disagreement, serial/generation overflow,
journal truncation, and memory-cap exhaustion all execute the existing full owner loop and preserve
source behavior.

### Oracle D6: semantic paired runs

Always-solve and scheduled modes compare schemes, candidate surfaces, selections, SCC events after
normal scheduling equivalence, diagnostics, lowering errors, and runtime results. Scheduler timing
counters are compared separately because skipped scans intentionally change performance stats.

### Oracle D7: workload and metamorphic coverage

The acceptance set from Decision 10 includes rename/module-move variants where resolution targets
remain equal. Scheduling must depend on structured IDs and mutation keys, not path/name strings or
fixture identity.

## 10. Performance and no-heavy-fixpoint audit

The design is acceptable only under these constraints:

- the whole-session unchanged case remains O(1) in the existing snapshot fields;
- a typed mutation is distributed once through its reverse subscribers;
- a clean owner check does not compact a root/role/candidate or rebuild exact vector snapshots;
- dependency capture occurs only while the real dirty owner solve already traverses those reads;
- method taint is built once per forced pass;
- candidate prerequisite dependencies are learned from the existing finite recursive search and do
  not add a second traversal;
- cleanup is proportional to the removed owner's recorded dependency list;
- no scheduler-specific solve-until-stable loop is added;
- no rigid/protected variable, blocked pair, or through flag is introduced;
- no missing invalidation is represented as `Any`, `Never`, predicate deletion, or a cached success;
  and
- budget failure disables optimization instead of increasing an unbounded cap.

The likely residual cost after activation is the shared method-taint rebuild. This document does not
assume that owner scheduling removes it. If measurements show taint dominates and total payoff misses
the gate, Stage 5 stops; it does not silently broaden into incremental taint.

## 11. Diagnostics and telemetry

Dirty scheduling is internal compiler scheduling. A cache miss, unknown mutation, or budget fallback
is not a source diagnostic.

Timing/debug telemetry should expose stable counters for:

- whole-session guard hits/misses;
- owner checks, clean skips, dirty solves, and non-cacheable solves;
- cacheable outcome kind;
- mutation events by dependency kind;
- owners dirtied per event and `InvalidateAll` reasons;
- method-taint rebuild/diff time;
- dependency/reverse-edge counts and peak retained bytes;
- stale-record evictions and cap fallbacks; and
- always-solve shadow mismatches.

Raw `DefId`, `TypeVar`, role paths, and `RoleResolutionKey` may appear in debug detail. Performance
and correctness gates use aggregate categories and structural fixture labels, not hard-coded IDs.

## 12. Rollback and compatibility

Stages 0-5 must leave default production scheduling unchanged. Stage 6 is the first default behavior
change.

If one false-clean case is found after activation:

1. disable owner skips while retaining the whole-session guard;
2. preserve the counterexample and its exact-snapshot shadow result;
3. classify whether read capture, a low-level mutation event, derived method-taint diff, reverse
   subscription replacement, or cleanup caused the miss;
4. add the missing structured dependency/mutation at the authoritative layer;
5. do not add a fixture/name/path special case or redefine the expected outcome; and
6. reactivate only after the complete acceptance set returns to zero mismatches.

The scheduler holds no serialized state and does not change source semantics, so rollback is removal
or disabling of the owner eligibility layer. It must not require reverting the eight independent
performance fixes or the `df1c23f3` guard.

## 13. Unconfirmed points and implementation blockers

The following are deliberately not guessed:

1. **Formal completeness beyond the measured fixtures.** Zero mismatches over 21,532 checks is
   strong evidence, but the current oracle compares terminal progress classification, not a formal
   proof over all future compact/role-solver reads. Stage 1 must make new read kinds fail contract
   coverage tests.
2. **Exact production recorder API.** A session-local constraint recorder plus explicit non-
   constraint collector is the proposed shape. The borrow/interface impact through compact and
   role-solve entrypoints needs Stage 1 validation. Always-on release TLS or full polling requires
   renewed approval.
3. **Complete low-level bounds/pruning/removal inventory.** Upper-row pruning and the row-effect
   no-replay upper insertion are known epoch gaps. Stage 1 may find other mutation paths where an
   observable vector changes without the current epoch. Stage 2 cannot complete until that
   inventory is closed.
4. **Direct mutable table access.** `AnalysisSession` currently exposes tables used directly by
   tests and some internal code. The exact infer-local wrapper/privacy migration must be chosen so
   production mutation cannot bypass journaling while read-only callers remain simple.
5. **Method-taint diff cost and stability.** Retaining and diffing the whole index should be much
   cheaper than owner solves, but this has not been measured. Its ordering and selection-list
   normalization need a deterministic witness.
6. **Root-unavailable cache value.** The architecture safely includes `SccRoot(owner)`, but all
   empirical checks had roots. Version 1 may conservatively decline to cache `RootUnavailable`
   until a focused lifecycle witness passes.
7. **Absolute memory and watchdog caps.** The policy is resolved; numeric owner, dependency,
   reverse-edge, journal, byte, and time limits require Stage 5 evidence and explicit approval.
8. **Time-weighted payoff.** The 97.78% clean-call rate does not by itself prove the same share of
   wall time is avoidable. Stage 0 is a hard continuation gate.
9. **Telemetry equivalence.** Semantic outputs must match, but raw role-solver scan counters will
   intentionally fall. Consumers of existing counters need an audit so skipped work is not mistaken
   for an unobserved solve.
10. **Future solver reads.** New candidate filters, constraint side tables, or taint predicates must
    add a dependency key/read hook before scheduler-enabled tests can pass. No default wildcard key
    should silently treat them as clean.

If any of these points requires polling the complete reachable constraint component or sharing
scheduler state with generalization/early fallback, the project must stop for a size/risk revision.

## 14. Overall size and risk

Overall estimate: **L, risk high**.

This refines the initial M-L/medium-high scoping estimate upward. The owner cache and pass wiring
alone remain M-L/medium-high. A sound production project also has to complete mutation contracts for
six constraint observables, derived method taint, SCC roots, owner/projection selections, owner role
tables, recursive candidate buckets, and applied-resolution membership. That cross-cutting contract
is the dominant size and correctness risk.

Expected blast radius is approximately 8-14 files and 900-1,700 lines including the scheduler,
mutation outboxes/wrappers, metrics, and adversarial tests. The estimate remains below the
two-stage lifecycle and suffix-safety-oracle projects in conceptual novelty: it does not pause
quantification, change role semantics, serialize inference state, or create a new proof kernel.

The high rating has three causes:

1. one missed invalidation can silently suppress a role resolution;
2. mutation coverage crosses several hot-path tables whose current epochs have different meanings;
3. the optimization must remain cheaper than the owner work it avoids.

If Stage 1 proves that authoritative mutations cannot be closed without invasive compact API or
table-ownership redesign, revise the estimate toward L-XL/very-high and stop before Stage 2. If the
typed journal fits the existing event/table boundaries and Stage 0 confirms time-weighted payoff,
the L/high estimate should hold.

## 15. Completion gates

The owner-level dirty scheduling project is complete only when:

- the actual shadow fingerprint and its limits remain documented and tested;
- every compact-observable read maps to a typed dependency;
- every authoritative observable mutation emits a typed key or `InvalidateAll`;
- upper pruning/removal and adjacency changes no longer bypass invalidation;
- only `RootUnavailable`/`NoProgress` terminal outcomes are cacheable;
- progressing owners retain the unchanged solver and fixed-point behavior;
- the whole-session guard remains the top-level fast path;
- method taint is rebuilt/diffed once per forced pass and not per owner;
- candidate prerequisite buckets invalidate transitively through actual reads;
- stale owner/reverse records are removed at selection/SCC/session boundaries;
- all unknown, overflowed, capped, or contract-mismatched states run the full owner pass;
- the complete correctness acceptance set has zero false-clean outcomes;
- semantic paired runs match always-solve mode;
- the approved wall-time and memory gates pass;
- no inference protection mechanism, second solver loop, name/path special case, or cross-session
  raw identity cache was added; and
- early fallback, intermediate generalization, stable demand identity, and incremental method taint
  remain separately scoped unless later reviewed.

Investigation and design: Codex (gpt-5.6-sol), 2026-07-15 session.

Implementation approval is pending Claude/user review. This attribution records the investigation
and draft specification only; it is not a Claude signature and does not approve starting any
implementation stage.

---

**Reference-specification approval (2026-07-15): Claude Sonnet 5 and the user reviewed this document and accept it as the reference specification for the owner-level dirty scheduling project.** This approval covers the architecture in Section 5, the ten decision-point resolutions in Section 6, the rejected-alternatives list in Section 7, and the staged plan in Section 8 (revised to L/high overall risk in Section 14) as the basis for future work. It does NOT constitute implementation approval for any stage — per Section 8's own text, every stage requires its own separate sign-off before implementation begins, and Stages 2 and later require explicit human sign-off individually per their stated approval class. The user has explicitly confirmed this project may span multiple sessions and that session continuity is not a concern; work should proceed stage by stage with the same verification rigor (test suite parity, semantic comparison, adversarial soundness tests) established throughout this project's other performance work this session. The project's own built-in escape valve (Section 14: if Stage 1 finds authoritative mutations cannot be closed without invasive compact API or table-ownership redesign, revise the estimate toward L-XL/very-high and stop before Stage 2) remains in force.

---
