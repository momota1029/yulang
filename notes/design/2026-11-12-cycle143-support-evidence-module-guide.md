# Cycle143: support-aware dictionary evidence

Fresh integration: 6cff680ccafc24ab298e1b890adcb6d7bba15034. I-25 remains active.
The target is the newly integrated support-aware V5 boundary, not the older
unguarded feedback/reobservation relation. Definitions remain Astra-owned.

## Modules planned

* `GeneralDictionarySupportEvidence`: recover actual guarded installation from
  support selection; derive same-model Evidence under explicit jointness;
  discharge residuals for packet-free Initial/Reachable states.
* `GeneralDictionarySupportJournal`: preserve each installed packet's Instance
  at its **stored** inspection context through actual guarded steps, including
  certified point reobservation. This is not a current-context theorem.
* `GeneralDictionarySupportRevisionObstruction`: test whether the prior
  nonempty Current failure is genuinely reachable under the new support guard.

The Current counterexample is not a counterexample to V5 Evidence. In
particular, historical packet validity and current local selection must not be
identified. General nonempty reachable Joint/current-context dictionary
construction remains a separately stated obligation unless proved this cycle.

Validation uses focused Lean builds, a new audit shard (not frozen Audit.lean),
and the no-build verification gate. No claim of full aggregate rebuild or new
Yulang2 execution is made.
