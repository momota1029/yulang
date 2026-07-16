# Generalization role-solve `ConstraintEpoch` completeness audit

Date: 2026-07-16

Scope: Stage 0 exit criteria 3 and 4 of
`notes/design/2026-07-16-generalize-role-resolve-snapshot-spec.md`, pursuing repair option (1).
This audit does not implement the snapshot cache and does not reuse or extend the owner-level
`constraints::mutation` journal.

## Verdict

Option (1) is sufficient. After the repairs recorded with this audit, an available
`ConstraintEpoch`, read at the existing drained generalization role-solve boundary, is a complete
coarse witness for every mutable constraint-machine resource read by the pure recursive role
solver. No separate role-associated-bound generation and no `E/M/D/C/A` guard are needed.

The exact eligibility condition is not bare integer equality. Both captured epochs must satisfy
`ConstraintEpoch::can_witness_unchanged_state()`, and the boundary must have no pending constraint
work or events. Saturation or a non-drained boundary makes the epoch unavailable and forces a full
solve. This remains the existing `E/M/D/C` shape: availability and quiescence are preconditions for
obtaining a usable `E`, not a fifth state dimension.

## Exact role-solver input inventory

| Recursive-solve input | Authoritative source | Guard mapping |
| --- | --- | --- |
| Normalized top-level demand, including its compact bounds | `roles` argument to `resolve_role_constraints*` | `D` |
| Main-variable polarity and negative co-occurrence pinning | `MainPolarity::collect(main)` | `M` |
| Candidate buckets, candidate heads/associated constraints, recursive prerequisites, and order | `RoleImplTable` | `C` |
| Candidate/prerequisite projected lower and upper bounds | `CompactCollector` over `ConstraintMachine::bounds` | `E` |
| Reachability through variables referenced by raw/compact roles | `ConstraintMachine::var_neighbors` | `E` |
| Row-upper item retention | `ConstraintMachine::subtracts` | `E` |
| Positive projection stack-family coexistence | `ConstraintMachine::pre_pop_effect_families` | `E` |
| Candidate simplification representative/floor decisions | current and birth `TypeLevel` | `E` |
| Direct raw candidate node heads and nested node structure | append-only `TypeArena` IDs held by `C` | immutable after allocation |
| Method-taint rejection | empty immutable map in the generalization entry point | no mutable input in this path |
| Applied resolution membership | live `applied` set read after pure result construction | deliberately downstream, not snapshot state |

`role_concrete_input_bounds` reads only `D`, the `MainPolarity` derived from `M`, and the empty
method-taint map on this path. `MainPolarity::collect` reads only `M`. Candidate compaction is the
only recursive-solve path that reads live constraint-machine state.

## Complete constraint mutation table

The table lists every effective mutation of a resource above, including derived neighbor changes.
The owner-scheduling mutation contract was used only as an independent inventory cross-check; its
journal, records, activation lifetime, and subscription model are not used by this project.

| Observable resource | Effective mutation path | Epoch coverage after repair | Notes |
| --- | --- | --- | --- |
| Regular lower bounds | `add_lower_bound` / `TypeBounds::add_lower` | global + variable | Includes promotion/removal of a matching evidence lower. |
| Regular upper bounds | `add_upper_bound` / `TypeBounds::add_upper` | global + variable | Includes promotion/removal of a matching evidence upper. |
| Evidence lower bounds | `apply_bound_replay_evidence_actions` | global + variable | Environment-gated path remains covered. |
| Evidence upper bounds | `apply_bound_replay_evidence_actions` | global + variable | Environment-gated path remains covered. |
| Selective row-match upper storage | `row_effect::store_upper_bound_without_replay` | global + variable | Repaired. Epoch publication does not enqueue replay. |
| Upper-row removal | `prune_upper_rows_subsumed_by_reduced_upper` | global + variable | Repaired at the authoritative vector mutation, including prune-without-successful-following-insert. |
| Neighbor absent-to-present transition | `record_var_neighbor` from accepted bound insertion | enclosing bound epoch | No independent production caller. Count-only changes do not change the observed neighbor key set. |
| Neighbor present-to-absent transition | `unrecord_var_neighbor` from upper-row pruning | enclosing pruning epoch | Repaired by the pruning mutation publication. No independent production caller. |
| Current level lowering | `TypeLevels::lower_to` in extrusion | global | Repaired directly, including a later subsumption/duplicate early return. |
| Current/birth level registration | `register_type_var` | global | Repaired only on first effective registration; re-registration remains a no-op. |
| Subtract fact insertion | `SubtractTable::record` | global | Already complete. Duplicate facts do not advance. |
| Pre-pop family insertion | `record_pre_pop_effect_families` | global | Already complete. Duplicate families do not advance. |

All projected-bound paths now call `record_effective_bounds_mutation`, which advances both the
global epoch and the variable's bounds epoch and emits the existing typed owner mutation when that
separate journal is active. This single authoritative publication point prevents ordinary,
evidence, pruning, and no-replay vectors from drifting apart again.

## Mutations deliberately outside `E`

- `TypeArena` allocation is append-only/hash-consed. There is no API that mutates a node already
  referenced by a candidate. An unrelated allocation cannot change candidate compaction.
- `seen`, `row_residuals`, `lower_filters`, `effect_filter_violations`, `declared_subtracts`,
  `effect_family_paths`, `row_tail_vars`, `next_internal_type_var`, timing, and replay shadows are
  not read by the pure recursive role solver. Any future projected bound, subtract fact, pre-pop
  family, or level mutation they cause enters through a covered path above.
- Queue insertion is not an observable solved state and does not advance the epoch. All external
  constraint mutators drain before returning; the internal queue cannot be populated outside the
  constraint module. The generalization characterization also records queue length and rejects a
  boundary with pending work.
- Constraint events are downstream publication work, not pure role-solver input. The established
  boundary rejects pending events; event-only cast/filter facts therefore cannot authorize reuse.
- Candidate-table mutation remains `C`. Main and normalized demand mutation remain `M` and `D`.

## Replay-termination safety

`store_upper_bound_without_replay` exists to avoid replaying the newly reduced row upper against
every lower after row matching has already selected original-versus-reduced replay targets. That
selective queueing policy is unchanged. `ConstraintMachine::bump_epoch` only increments a counter;
it does not enqueue work, add a bound, emit an event, or consult the replay frontier. Publishing the
already-effective vector mutation therefore cannot reintroduce the replay explosion addressed by
the directed-stack-weight/replay-termination work.

Upper-row pruning is similarly unchanged. The repair publishes a counter after the existing
vector and neighbor removals; it does not change which rows are pruned or which constraints replay.

## Proof obligations and regression witnesses

- `snapshot_constraint_epoch_covers_row_match_candidate_bound_mutation` preserves the committed
  production-reachable associated-position counterexample. Unchanged inputs reproduce the same
  result; the row-match mutation changes both the epoch and the pure result.
- `snapshot_constraint_epoch_covers_candidate_level_registration` shows that candidate
  simplification can observe a level-registration change and that the global epoch now changes
  with it.
- `constraint_epoch_covers_level_registration_and_lowering` covers effective registration,
  no-op re-registration, and direct current-level lowering.
- `constraint_epoch_covers_upper_row_pruning_and_neighbor_removal` covers the exact upper vector,
  its per-variable epoch, the global epoch, and derived neighbor removal.
- `saturated_constraint_epoch_cannot_witness_unchanged_state` locks the fail-closed overflow rule.
- The existing full acceptance-set characterization continues to require zero pure-result
  mismatches under eligible equal `E/M/D/C` and rejects boundaries with pending constraint work or
  events.

## Stage 0 criteria 3 and 4

Criterion 3 is satisfied by the exact input inventory above: all recursive-result inputs map to
`E`, `M`, `D`, or `C`; method taint is immutable-empty on this path, and applied membership remains
the already-tested live downstream disposition input.

Criterion 4 is satisfied by the repaired complete mutation table plus the fail-closed availability
conditions. Equality of two non-saturated epochs obtained at drained, event-free boundaries proves
that none of the live constraint resources consumed by candidate/prerequisite compaction changed.
The broader owner-scheduling mutation journal is not required, so Sections 5.2/13.2 do not trigger
a separate size/risk review for these two criteria.
