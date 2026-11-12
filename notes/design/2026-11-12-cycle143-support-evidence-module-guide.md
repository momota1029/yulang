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

## Verified reduction and remaining obligation

The implementation obtains `Slice state (dependencyPool state) = Models
state.current` from actual source formation's `Exact` invariant. The existing
Astra `MergeGuard` has no `Admissible` clause, so the full finite dependency pool
is a legal merge support. This proves merge closure from support-stability;
old feedback stability is not assumed. The selected root's `PacketGuard` is
constructed separately from its `DecisionGuard`, which does have admissibility.

For a nonempty reachable snapshot, `reachable_joint_evidence` now retains only
`Joint` and same-final-model child evidence. `Joint` means BOTH:
1. Every already stored packet aliased to the focus has the selected key.
2. ONE model satisfies the current journal, the focus branch, and the same-key
   branch at EVERY aliased site, including all named-output obligations.
A separate existential branch model for each occurrence is insufficient.

The packet-free actual reachable case discharges this entirely and forces the
selected child list to be empty. The guarded nonempty Current obstruction
retains its historical packet Instance in the same modeled final state. This
shows why historical and literal-current packet semantics must remain distinct,
not that current V5 Evidence fails. Stable is not proved for that fixture.

Independent read-only review found no hidden old-stability premise or defect.
The interpretation of the full-pool merge witness relies specifically on the
current Astra MergeGuard definition and is not claimed for a stronger guard.

## Recursive and whole-target composition

`GeneralDictionarySupportTree` carries generated membership and support-stability
through a finite selected `Classify` dictionary by size induction. Joint is
needed only at selected generated nodes of the fixed reachable snapshot. Its
packet-free specialization has no Joint premise and proves terminal tree shape.

`GeneralDictionarySupportComposition` inserts these dictionary obligations into
the actual `B4SkeletonV5` fields. It does not assume EvidenceNode as a premise.
The full V5 statement remains conditional on FOUR named obligations: Progress,
where-child accessibility, canonical final-local order, and simultaneous Joint
at stable selected generated occurrences. The existing noncomputable driver
supplies execution/halted/treeExecution under Progress. Neither these explicit
hypotheses nor the composition theorem close the general-language theorem.

`GeneralDictionarySupportCompletionGap` rules out another overstrong shortcut:
actual reachability plus a genuine model does not imply ContextComplete. It
asserts neither Stable nor final selectedness, and is not a V5 counterexample.

A concrete source-supported repaired refresh-fork example is next: both actual
paths reach a packet-free stable selected point observation, allowing the new
unconditional packet-free dictionary theorem to be exercised on real data.

The concrete fork is now verified in `GeneralDictionarySupportForkExample`:
source-entailed refresh recovers head0, inspection reads exactly `[0,2,3]`, and
an empty producer support supplies the real DecisionGuard. Wide observation is
not stable because the certified point revision is enabled. The point state is
actually reachable, inhabited, stable, selected90[], and has terminal Evidence.

`GeneralDictionarySupportInhabitation` verifies that InitialSource itself has no
inhabitation requirement: a concrete initial source with ordinary int≤str is
reachable and has no model. Accordingly the recursive snapshot tree result
requires Joint only when that snapshot has a model. The whole-target
GeneratedChildren field is model-free, so the composition's global Joint
assumption is deliberately not weakened using an unavailable model witness.

Stored declaration visibility is also preserved through all support updates.
For a singleton registry this removes the key-coherence half of Joint without
assuming Current; the simultaneous model for all alias branches still remains.
