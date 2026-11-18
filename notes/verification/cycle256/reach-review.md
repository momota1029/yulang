# Read-only reachability analysis

Cycle256Reach.lean follows declaration dependencies from15 selected new result
roots.88/101 explicit declarations are reached. The13 outside that selected set
are listed in reach.txt. This is not a claim that they are unused or removable.

- report_prepared/frame_prepared/identity_fits: alternative public wrappers.
- HistoricalAggregate.finite and AggregateBasis.prepared_finite: finite-menu APIs
  stated separately from semantic preservation; keeping this distinction avoids
  promoting unconditional finiteness into unconditional correctness.
- ReachableAggregate.frame/reachable_all: actual source-frame/reachability entry
  points explicitly exercised by Usage, separate from the indexed-family value
  lemmas in the chosen roots.
- pool_unique, outside_initial_names, erased_row_sources: concrete representation
  checks, some used in direct Usage or available independently.
- ordinary_unchanged/nominals_unchanged/slot_count: literal field/multiplicity
  APIs documenting exactly what the new representation did not change.

No module/declaration was deleted. Frozen Main/outer B4 statements are not
claimed to depend on these helpers already; the all-source invariant and actual
successor bridges remain open. This selected-new-root analysis is narrower than
a whole-repository Main/Audit reachability census and does not replace it.
