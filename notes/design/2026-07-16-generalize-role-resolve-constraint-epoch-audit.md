# Generalization role-solve constraint witness audit

Date: 2026-07-16

Scope: Stage 0 exit criteria 3 and 4 of
`notes/design/2026-07-16-generalize-role-resolve-snapshot-spec.md`, starting with repair option (1).
This audit does not implement the snapshot cache and does not reuse or extend the owner-level
`constraints::mutation` journal.

## Verdict

The existing `ConstraintEpoch` cannot safely be made complete without changing its established
production semantics. Four role-solver-observable mutation classes were missing from it. Adding all
four to the global epoch made
`role_impl_conformance_concrete_anchor_witness_requires_bidirectional_nominal_evidence` fail; a clean
`4185950f` export passed the same isolated test. The minimal reproducer was the first effective
`register_type_var` bump alone.

The reason is concrete: the global epoch is already consumed by method-role pass snapshots,
`FinalRoleSolveSnapshot`, and the owner mutation-journal audit fence. It is not a passive diagnostic
counter. Expanding it can force different production invalidation/audit paths even though it does
not enqueue constraint replay.

Stage 0 criteria 3 and 4 are nevertheless satisfied by a narrow hybrid witness:

```text
E = existing ConstraintEpoch
A = RoleSolveSupplementalEpoch for the four facts intentionally absent from E
M = exact post-floor main
D = exact normalized demand
C = candidate-table generation
```

`A` is a saturating global counter with no replay, lifecycle-audit, owner-scheduler, or cache
semantics. It advances only for first level/birth registration, effective current-level lowering,
upper-row pruning, and selective no-replay row-upper insertion. Snapshot reuse must compare both
`E` and `A`; neither is complete alone. Saturation of either counter, pending constraint work, or
pending constraint events makes the boundary ineligible.

This is an `E/M/D/C/A` design, not a repaired bare `E/M/D/C` design. It is also not option (2): it
does not consume dependency keys, subscriptions, outboxes, mutation serials, or owner records from
`constraints::mutation`.

## Exact role-solver input inventory

| Recursive-solve input | Authoritative source | Guard mapping |
| --- | --- | --- |
| Normalized top-level demand, including compact bounds | `roles` argument to `resolve_role_constraints*` | `D` |
| Main-variable polarity and negative co-occurrence pinning | `MainPolarity::collect(main)` | `M` |
| Candidate buckets, heads, associated constraints, recursive prerequisites, and order | `RoleImplTable` | `C` |
| Candidate/prerequisite projected lower and upper bounds | `CompactCollector` over `ConstraintMachine::bounds` | `E` or `A`, by mutator |
| Reachability through variables referenced by roles | `ConstraintMachine::var_neighbors` | enclosing bound mutation in `E` or `A` |
| Row-upper item retention | `ConstraintMachine::subtracts` | `E` |
| Positive projection stack-family coexistence | `ConstraintMachine::pre_pop_effect_families` | `E` |
| Candidate simplification representative/floor decisions | current and birth `TypeLevel` | `A` |
| Direct raw candidate node heads and nested node structure | append-only `TypeArena` IDs held by `C` | immutable after allocation |
| Method-taint rejection | empty immutable map in the generalization entry point | no mutable input on this path |
| Applied resolution membership | live `applied` set read after pure result construction | deliberately downstream, not snapshot state |

`role_concrete_input_bounds` reads only `D`, `MainPolarity` derived from `M`, and the empty
method-taint map on this path. `MainPolarity::collect` reads only `M`. Candidate compaction is the
only recursive-solve path that reads live constraint-machine state.

## Complete mutation-path audit

The owner-level dirty-scheduling mutation matrix was used only as an independent inventory
cross-check. Its journal remains a separate design with a separate lifetime and cost model.

| Observable resource | Effective mutation path | Legacy `E` before audit | Final witness | Safety/result |
| --- | --- | --- | --- | --- |
| Regular lower bounds | `add_lower_bound` / `TypeBounds::add_lower` | global + variable | `E` | Already complete; evidence promotion included. |
| Regular upper bounds | `add_upper_bound` / `TypeBounds::add_upper` | global + variable | `E` | Already complete; evidence promotion included. |
| Evidence lower bounds | `apply_bound_replay_evidence_actions` | global + variable | `E` | Already complete. |
| Evidence upper bounds | `apply_bound_replay_evidence_actions` | global + variable | `E` | Already complete. |
| Selective row-match upper storage | `row_effect::store_upper_bound_without_replay` | none | `A` | Global bump rejected; supplemental bump does not alter selective replay. |
| Upper-row removal | `prune_upper_rows_subsumed_by_reduced_upper` | none | `A` | Covers prune even if a following insertion is rejected. |
| Neighbor absent-to-present | accepted ordinary bound insertion | enclosing bound epoch | `E` | No independent production caller. |
| Neighbor absent-to-present | accepted no-replay row upper | none | `A` | Same authoritative mutation as the upper insertion. |
| Neighbor present-to-absent | upper-row pruning | none | `A` | Count-only changes do not change the observed key set. |
| Current level lowering | `TypeLevels::lower_to` in extrusion | none | `A` | Covers lowering followed by a duplicate/subsumed bound return. |
| Current/birth level registration | `register_type_var` | none | `A` | First effective registration only; re-registration remains a no-op. |
| Subtract fact insertion | `SubtractTable::record` | global | `E` | Already complete; duplicates do not advance. |
| Pre-pop family insertion | `record_pre_pop_effect_families` | global | `E` | Already complete; duplicates do not advance. |

Ordinary and evidence bound publication is centralized in
`record_effective_bounds_mutation`; that refactor preserves the legacy global/per-variable epoch
and optional journal behavior. The four supplemental sites deliberately do not call it.

## Why blanket global-epoch repair is unsafe

`store_upper_bound_without_replay` exists to avoid replaying a reduced row upper against every
lower after row matching has already selected original-versus-reduced replay targets. A counter
increment itself does not enqueue replay, so the replay-termination invariant is not the direct
blocker.

The blocker is existing consumers of `ConstraintEpoch`:

- method-role pass input snapshots use equality to skip a no-progress pass;
- `FinalRoleSolveSnapshot` uses equality in its production reuse gate;
- `sync_method_role_mutation_outboxes` compares it with the last audited epoch and emits
  `AuditFenceDisagreement` when the epoch changed without the journal generation changing.

The attempted first-registration bump changed this production control flow and failed the isolated
conformance test. Keeping that bump would therefore change more than “make a diagnostic counter
honest,” contrary to this task's safety condition. Fixing the downstream conformance/audit behavior
would be a separate project, not a Stage 0 witness repair.

`RoleSolveSupplementalEpoch` avoids that coupling. It performs one saturating increment at an
already-effective mutation and is read only by the test-only Stage 0 characterization. It does not
change queues, events, bounds, replay routing, journal generations, or existing cache decisions.

## State deliberately outside the pair `E/A`

- `TypeArena` allocation is append-only/hash-consed. There is no API that mutates a node already
  referenced by a candidate. An unrelated allocation cannot change candidate compaction.
- `seen`, `row_residuals`, `lower_filters`, `effect_filter_violations`, `declared_subtracts`,
  `effect_family_paths`, `row_tail_vars`, `next_internal_type_var`, timing, and replay shadows are
  not read by the pure recursive role solver. Any role-observable mutation they cause enters a
  covered bound, subtract, pre-pop, or level path above.
- Queue insertion is not solved state. All public constraint mutators drain before returning, the
  queue is private to the constraint module, and the Stage 0 boundary rejects pending work.
- Constraint events are downstream publication work rather than pure recursive-solver input. The
  boundary rejects pending events.
- Candidate-table mutation remains `C`; main and demand mutation remain `M` and `D`.

## Proof obligations and regression witnesses

- `snapshot_supplemental_epoch_covers_row_match_candidate_bound_mutation` preserves the committed
  production-reachable associated-position counterexample: repeat inputs return the same result;
  the no-replay mutation leaves `E` equal, advances `A`, and changes the pure result.
- `snapshot_supplemental_epoch_covers_candidate_level_registration` proves the same relationship
  for candidate-side level registration.
- `role_solve_supplemental_epoch_covers_level_registration_and_lowering` covers effective
  registration, no-op re-registration, and current-level lowering while locking legacy `E` equality.
- `role_solve_supplemental_epoch_covers_upper_row_pruning_and_neighbor_removal` covers the exact
  vector and derived neighbor removal while locking the legacy global/per-variable epochs equal.
- `saturated_constraint_epoch_cannot_witness_unchanged_state` locks fail-closed saturation for both
  counters.
- The full acceptance-set characterization requires zero pure-result mismatches under eligible
  equal `E/M/D/C/A` and rejects pending constraint work or events.
- The isolated conformance regression passes again with the hybrid and passes at parent
  `4185950f`, proving that existing `E` behavior has been restored.

## Verification

- The four focused supplemental-epoch adversaries pass, as do the saturation test and both legacy
  owner-oracle blind-spot characterizations.
- A fresh `4185950f` export passes the isolated conformance test. The attempted global registration
  bump fails it; the final hybrid passes it.
- The complete Stage 0 acceptance-set characterization passes with zero exact-result mismatches.
  Markdown iteration 3 and iteration 4 have equal `E`, equal `A`, and equal candidate generation;
  iteration 4 retains an exact-repeat witness.
- `cargo test -p infer --lib -- --test-threads=1` finishes with 817 passed and only the five known
  unrelated Yumark `DefId`-ordering failures.

The same debug characterization invocation was run at parent `4185950f` and again with the hybrid.
These are single-run wall samples rather than a release benchmark, but they show no systematic
fixed-cost regression:

| Fixture | `4185950f` baseline wall | Hybrid repeat baseline wall | Delta |
| --- | ---: | ---: | ---: |
| Markdown | 17.027 s | 16.091 s | -5.50% |
| HTML | 6.507 s | 6.011 s | -7.62% |
| Repository std only | 5.554 s | 5.481 s | -1.31% |
| Showcase | 5.527 s | 5.681 s | +2.79% |

The first hybrid sample was materially slower while unchanged recursive role-solve time also rose;
an immediate repeat after the parent sample reversed that result on three of four fixtures. The
supplemental work is one saturating increment at each of the four relevant mutation classes, and
the paired samples do not support attributing a production regression to it.

## Stage 0 criteria 3 and 4

Criterion 3 is satisfied by the exact input inventory above. Every recursive-result input maps to
`E`, `M`, `D`, `C`, or the narrowly-defined `A`; method taint is immutable-empty on this path, and
applied membership remains the live downstream disposition input.

Criterion 4 is satisfied by the complete mutation table and fail-closed eligibility rules. Equality
of available `E` and `A` at drained, event-free boundaries proves that none of the live constraint
resources consumed by candidate/prerequisite compaction changed. Literal bare-`ConstraintEpoch`
option (1) is rejected, but the bounded hybrid is sufficient; escalation to the broader mutation
journal in option (2) is not required for Stage 0.
