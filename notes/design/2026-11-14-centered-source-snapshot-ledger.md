# Exact snapshot support cannot be completed by a trusted ledger

Status: Lean-certified obstruction to the proposed invariant repair. The
full-frontier snapshot-supported initializer and conditional input promotion
are proved, but the snapshot-support property cannot be preserved through every
actual centered transition. Proof search stopped at this obstruction.
Unconditional `Simulation`, `ClassPSourceProduction`, and Class P accessibility
remain open. No transition, boundary, trust rule, or existing target was changed.

## Result and scope

The new module `GeneralNominalCenteredSourceLedgerObstruction` proves more than
failure of the previous empty selected ledger:

- `centered_trusted_source_models`: every original-source model satisfies
  **every** selected centered `Trusted` ledger at the concrete refreshed state.
  This covers legacy raw facts and arbitrarily repeated input facts.
- `no_trusted_readbackR`: none of these ledgers supports exact input readback for
  the actual R candidate.
- `no_snapshot_ledger`: there is no trusted ledger validating the current cached
  head observations.
- `no_snapshot_coverage`: for every inventory and journal, the new `Coverage''`
  is impossible at that reachable runtime state.
- `refresh_preservation_counterexample`: a real refresh starts with a trusted
  ledger and exact snapshot support, yet no trusted ledger can supply exact
  snapshot support afterward.
- `no_preserved_exact_input_invariant`: no state predicate containing the
  initializer and preserved by every real Step can imply exact trusted input
  readback at every executable guarded nonterminal installation, even when each
  installation may choose its own ledger existentially.

The last result is independent of inventories, labels, and any arbitrary choice
of an auxiliary journal. Its `ExecutableReadbacks` projection is restricted to
actual generated, installable, novel, guarded nonterminal candidates. Thus making
the snapshot condition candidate-specific instead of covering every cached head
cannot fix the obstruction.

These statements do not refute accessibility or a source-production proof using
a different interface. They do not refute `InputReadbackAndOrigins''`, which
assumes exact snapshot support; that proposition's new-origin conjunct remains
open. What fails is maintaining its exact-snapshot premise along all actual
Steps under the existing `Trusted` relation. No source divergence or new
language-owner decision is established.

## Proposed invariants and positive proofs

`GeneralNominalCenteredSourceSnapshotLedger` defines two distinct properties.

`LedgerComplete` is the suggested syntactic candidate: every installed plan's
input and output facts belong to the selected centered ledger, and every
recorded raw merge is included as a legacy merge fact. `LedgerComplete.initial`
proves it for the empty initializer. `LedgerComplete.settled` proves that any
such **trusted** complete ledger forces every installed plan to be settled.
No equality between its coarse models and full state models is assumed or
claimed.

The chosen `Coverage''` instead extends the previous retained `Coverage'` with
`SnapshotReadbacks`: each exact cached `Head` observation holds in every model
of the selected coarse centered ledger. This does not prescribe which facts
must appear in the list. It addresses observation support rather than requiring
all installed output facts indiscriminately. The separate candidate-only
`ExecutableReadbacks` condition is narrower still.

The following positive results are proved:

- `SnapshotReadbacks.initial`: every initial cached head is supported by the
  original source, independently of which extra facts are selected.
- `SnapshotReadbacks.strengthen`: adding facts preserves already proved snapshot
  support.
- `SnapshotReadbacks.readback`: when a plan uses the current context, snapshot
  support gives the exact full-report readback required by `Trusted.input`.
- `initialized`: every point `InitialSource` has a valid full-frontier inventory,
  initial journal, and `Coverage''`. Its retention component still excludes
  the first turn's missing-original-hole counterexample.
- `input_readback`: specializes exact readback to a real bundled installation.
- `trusted_input`: extends the ledger with that installation's input fact, using
  the actual guard to derive recording, old trusted transport, and exact
  snapshot readback. No settled-output premise is needed to select an input.
- `Coverage''.executable`: snapshot-supported coverage supplies the existential
  exact-readback projection at every executable guarded nonterminal candidate.

`InputReadbackAndOrigins''` is restated over the previous installation bundle,
retention, and exact snapshot support. Its readback conjunct is proved by
`input_readback`. The new-origin conjunct is not proved. The earlier
`GeneralNominalCenteredSourceLiveProduction.original_input` still supplies values
for directly named original sources under retention; it does not supply all
fresh binders or projection origins.

The old missing-hole inventory is excluded by `previous_inventory_excluded`.
The second example's empty ledger is excluded by `empty_ledger_incomplete` and
`empty_ledger_not_snapshot`. The stronger universal results show that merely
selecting a larger trusted ledger cannot replace that empty ledger successfully.

## Why complete output selection fails

The existing `GeneralNominalCenteredSupport.Trusted.output` constructor requires
`PacketSettled` for the exact output packet. The existing theorem
`outputs_settled` propagates this condition to every selected output fact.
Installation itself does not settle children.

The concrete P packet has an uninstalled R child. `no_discharge` proves by
induction on finite discharge evidence that no occurrence is discharged at the
refreshed state: the only installed packet is P, and discharging it would first
require discharging its child; aliases cannot supply a base case. Thus no packet
is settled there. Settlement transport along the actual refresh also gives
`no_settled_after_install` for the state immediately after P installation.

Consequently `no_complete_ledger_after_install` refutes the proposed complete
trusted ledger immediately after the first actual installation, and
`no_complete_ledger` refutes it at the refreshed state. An unconditional trusted
extension adding all installed output facts cannot be proved under the frozen
trust rules. This is a formal incompatibility with the proposed proof invariant,
not an added deferral rule.

## Concrete source and the universal countermodel

The checked source shape is schematic Yulang, not a parser fixture:

```text
impl P[Pair[A, C]] where R[A, Out = B] { Out = B }
impl R[Pair[X, Y]] where S[X]         { Out = X }

root demand: P[Pair[Pair[?u, ?u], ?u], Out = ?u]
```

The frozen witness module from the previous turn supplies:

```text
initial source: 0 = Pair(1,2), 1 = Pair(2,2), 2 = ?u
additional slot: 3 = Int, initially without a cached known head
actual trace: install P; refresh; install R
```

The emitted R site's explicit center is `1`. P's fresh output center `b` is
constrained to equal `?u` by full runtime output equations. The actual refresh
uses those full models to cache `1 = Pair(b,b)` and exposes the independent Int
slot to provide strict progress. R's candidate readiness already has a source
explanation for the pair head through the original `1 = Pair(?u,?u)`.
All guards, novelty, cycle safety, and consistency witnesses for both installs
and the refresh are proved in the frozen witness; no actual transition is an
extra hypothesis of the final counterexample.

`recorded_facts` proves that the available raw facts are exactly P's input and
output facts. There is no recorded merge. P output trust is impossible because
R is unsettled. Every remaining raw input fact and centered P input fact holds
in every original-source model. Induction over both raw and centered trust
therefore proves `centered_trusted_source_models`.

In particular, the existing `bad` model assigns `?u = Int` and
`b = Pair(Int,Int)`. It preserves every original source while violating the
exact refreshed observation `1 = Pair(b,b)`. It satisfies every trusted selected
ledger, not just the empty one. This proves the exact-readback obstruction even
for the actual enabled, guarded R installation.

`head_before_refresh` and `snapshot_before_refresh` show that every cached head
before that actual refresh has original-source support. Thus the failed
preservation case is explicitly a refresh from a supported state; it is not a
failure to initialize or a missing original frontier hole. The explicit center
remains present throughout. No missing-provenance argument is used.

The final `counterexample` theorem packages `Checked`, point `InitialSource`,
a certified unknown input, reachability, the actual next centered Step, and the
absence of any trusted ledger supplying exact R input readback.

## Remaining obligations and stop point

The exact remaining premises of the positive input lemmas are:

- `input_readback` and `trusted_input`: the bundled actual installation and
  `SnapshotReadbacks` for its already selected ledger.
- `InputReadbackAndOrigins''`: its origin-production conjunct remains unproved;
  the proposition as a whole is neither proved nor refuted.
- `LedgerComplete.settled`: a complete selected list, its existing `Trusted`
  certificate, and membership of the plan. It does not construct trust.

Preservation of trusted completeness and snapshot-supported coverage through all
constructors is false, by the certificates above. Later full-report exposure,
K2-safe constructor production, capture reconciliation, `CommonCaptures`, and
unconditional nonterminal installation preservation were not pursued after the
stop condition. No new `NonterminalInstallPreservation''` or unconditional
`Simulation`/accessibility theorem is claimed. The previous conditional reduction
still carries `NonterminalInstallPreservation'` (universally,
`ClassPInstallPreservation'`); its staged route still carries
`FullReportExposures'` and `CaptureReconciliation'` in addition to input production.

A continuation must change the exact-readback proof interface or supply another
source-production argument. Strengthening only the maintained invariant while
keeping this exact trusted-readback requirement cannot succeed on the actual
transition relation. The current result supplies no basis for changing language
semantics or claiming an infinite execution.

## Checks and repository scope

Final commands from `lean/`:

```text
lake build --wfail Yulang.GeneralNominalCenteredSourceSnapshotLedger Yulang.GeneralNominalCenteredSourceLedgerObstruction
exit 0 (901 jobs)

lake build --wfail Yulang > /tmp/yulang-source-snapshot-build.log 2>&1
exit 0 (2408 jobs)

lake env lean Audit/CenteredSourceSnapshotLedger.lean > /tmp/yulang-source-snapshot-audit.log 2>&1
exit 0
```

The new audit checks all 38 new theorem/definition declarations, including all
ten probe lemmas and the final preservation obstructions. Dependencies are
limited to `propext`, `Classical.choice`, and `Quot.sound`.

During elaboration, `lake env lean Yulang/GeneralNominalCenteredSourceSnapshotLedger.lean`
and the first `lake build --wfail Yulang.GeneralNominalCenteredSourceLedgerObstruction`
returned exit 1 for implicit-argument inference errors. Those were corrected;
the individual module builds and the final combined build returned exit 0.
The independent concrete probe compiled with exit 0 before integration.

Both new names were checked against the entire locally available
`refs/remotes/origin/integration/m1-final` tree at
`122b0fabd725514c5bdcc638d539773610fcd040`, with no collision. No network update,
git reference change, commit, or frozen-file edit was performed.

The Yulang proof skill was used. No configured or callable `prover` role was
available, so no prover agent is claimed. The primary constructed the invariant
and final reductions; a separate agent constructed the universal-ledger probe.
A fresh independent review of the concrete probe and both final modules passed,
including the distinction between failure of snapshot preservation and the
unproved conditional `InputReadbackAndOrigins''` proposition.

`git diff --check` exited 0. Baseline-prefix, module-import, proof-token, and
name-collision checks exited 0. HEAD remains
`ab3a97af85192aec3b3e817c83e5867fd2a1fb88`; the only previously tracked files
changed are `lean/Yulang.lean` and `notes/design/INDEX.md`, both by appending.

## Exact theorem names

`Yulang.GeneralNominalCenteredSourceSnapshotLedger`:

- `LedgerComplete.initial`
- `LedgerComplete.settled`
- `SnapshotReadbacks.initial`
- `SnapshotReadbacks.strengthen`
- `SnapshotReadbacks.readback`
- `initialized`
- `input_readback`
- `trusted_input`
- `Coverage''.executable`

`Yulang.GeneralNominalCenteredSourceLedgerObstruction`:

- `recorded_facts`
- `no_discharge`
- `no_settled_packet`
- `no_merge_fact`
- `raw_trusted_source_models`
- `shared_trusted_source_models`
- `centered_trusted_source_models`
- `bad_every_trusted`
- `no_trusted_readbackR`
- `no_trusted_exact_observation`
- `no_settled_after_install`
- `no_complete_ledger_after_install`
- `no_complete_ledger`
- `empty_ledger_incomplete`
- `no_snapshot_ledger`
- `empty_ledger_not_snapshot`
- `no_snapshot_coverage`
- `previous_inventory_excluded`
- `head_before_refresh`
- `snapshot_before_refresh`
- `refresh_preservation_counterexample`
- `no_executable_readbacks`
- `no_preserved_exact_input_invariant`
- `unknown_input`
- `counterexample`

