# Centered production and terminal observation limits

Status: proved reductions and an actual terminal counterexample to the stronger
observation-confluence route. The G′ boundary and its unrestricted Step are
unchanged. Its unconditional V5 count remains eleven in this worktree; neither
of the two requested remaining fields is closed here. The separate evidence
worker's result is outside this change.

## Production: what is now unconditional

The governing [roles decisions](../../spec/06-roles.md) require
「同じ入力の需要はまとめる」 and 「impl を選ぶ前、保留のままでも行う」.
The center decision states 「実装が共有の情報を失ったことを理由に需要を保留にする規則は足さない」.
This work adds no pending or rejection condition.

`GeneralNominalCenteredCommitment` proves:

* Commitment of a **fixed packet**, including its actual child edges, persists
  through every centered action and finite trace.
* Every packet recorded in a reachable raw journal is committed there.
* Every child of such a packet is generated from any root that generated its
  parent. This is actual edge membership, not just candidate emission.
* At a halted snapshot, every generated installable packet is committed.

These facts use raw model restriction and persistent edges from the actual
centered Step. They do not identify a stored old packet with a current packet
after descriptor revision.

`GeneralNominalCenteredSelectedCompletion.selected_frame` constructs an exact
current packet from reachable, generated G′ selection, with **no** production
premise. `Frame r s d key children plan` records:

* the exact registry and current context;
* occurrence `d`, declaration key `key`, and exactly `children`;
* the registered raw site and its registered centered mate;
* visibility, role, located bounds, and Prepared.

For this frame, the following is proved:

```lean
GeneralNominalCenteredBoundary.Installable r s plan ↔
  GeneralNominalJointCandidates.Joint r s.erased.current
    plan.packet.site.occurrence plan.packet.declaration.id ∧
  ∃ support, GeneralNominalValueSupport.PacketGuard s.erased plan.packet support ∧
    ∃ model, GeneralNominalCenteredSteps.Models s model ∧ plan.Holds model
```

The right side is `Completion r s plan`. Selection supplies the required merge
closure, decision and actual-inspection guards. Completion is now existential
for one exact plan, rather than the earlier universal requirement on every
old-installable plan.

The unconditional theorem `stable_selected_commitment_or_obstruction` covers
**all** reachable, generated, stable selected demands, including leaves. It
constructs a Frame and proves that its packet is committed, or Joint fails,
or every old value-support certificate fails, or no common centered branch
model exists. This diagnoses the exact remaining guards; it does not establish
that their failures are unreachable.

The single remaining production lemma is `UncoveredCompletion roles`:

```lean
∀ r, (boundary roles).Checked r → ∀ s root d key children,
  B4TargetV5.Reachable (boundary roles) r root s →
  Generated s.erased.current root d → Stable r s d →
  Local r s d (.selected key children) → children ≠ [] →
  (¬ ∃ plan, Frame r s d key children plan ∧
    GeneralNominalFeedbackSteps.Committed s.erased.current plan.packet) →
  ∃ plan, Frame r s d key children plan ∧ Completion r s plan
```

This remains an **assumed progress obligation**, not a constructed producer.
It exempts leaves and already committed **exact current-context framed
packets**, not arbitrary historical installations. `stable_selected_committed`
and `generatedChildren` derive the requested exact commitment/child generation
from it. The earlier `ReachableProduction` implies this weaker obligation.
General extension of a current Prepared witness through all historical center
equations, jointly with alias-class branches and admissible support, is still
the missing construction. No stable reachable counterexample to production
is claimed.

## Required merging

`GeneralNominalCenteredMergeAvailability.merge_guard_iff` proves the precise
operational test for centered sites:

```lean
SupportChoices.MergeGuard s.erased first.observed last.observed support ↔
  Centers.SameInputs (Support.Slice s.erased support) first last
```

Every observed center is named, so recovery preserves its inputs and the
recovery-support obligations are vacuous. If two registered sites have the
same role and identical ordered center names, empty support suffices: an
actual centered merge Step exists whenever the first is generated and they
are not aliased. Consequently stability implies their aliasing. This requires
neither checked declarations nor a model-existence assumption.

For distinct center names known equal only in centered Models, equality in a
raw support slice remains required. The raw Slice contains old input/output
facts but not the centered plan-equation ledger. No general theorem equating
those two predicates has been proved. G′ selection already requires merging
to be closed; these lemmas do not turn an unavailable merge into an approved
final pending outcome.

## A real terminal fork defeats full observation agreement

The proposed semantic closure argument cannot establish agreement of every
primitive observation for arbitrary terminal states. The new fixture uses
these source identities:

| Source | Observation |
| --- | --- |
| 0 | `list` with invariant interval `(1,2)` |
| 1 | `int` |
| 2 | `int` |

The saturation root is occurrence 700, role 3, with point argument `(1,1)`.
The checked registry contains only the ordinary Display declaration
`Display (list a) where Display a` (role 0, key 1). Source formation and the
ground label `[int]` for the root are proved, rather than assumed.

Two actual `.administrative (.reobserve ...)` steps replace the descriptor at
source 0 by `(1,1)` and `(2,2)`, respectively. Both replacements are certified
model-equivalent. Every source is known, every nominal descriptor is a point,
and only the unmatched role-3 root is generated. The proof rules out **every**
centered transition constructor in both final states. Both final model sets
are inhabited and identical.

Consider the separate, **unregistered** Display observer, occurrence 100,
with argument `(0,0)`. Its Survivor emits a child with argument `(1,1)` in one
terminal state and `(2,2)` in the other. The two child identities are the same
and their inputs denote equivalent types in every model, but the literal
child lists are different. `Survivor` functionality proves disagreement.

`same_committed` additionally proves equivalence of Committed for **every
fixed raw packet** across these two states. Thus this is not merely equality
of empty stored packet lists. Equal models and equal committed-packet sets
still do not determine the all-demand primitive observations.

The resulting theorem is:

```lean
¬ GeneralNominalCenteredTerminalAgreement.TerminalObservationConfluence
    GeneralDeclarationExamples.roles
```

Here `TerminalObservationConfluence` quantifies over arbitrary pairs of halted
traces from the same ground initial source and reordered registries. The
counterexample even uses the reflexive registry reorder. It is not a failure
of the owner's declaration-order decision: the observer is unregistered and
cannot be selected by G′. Nor is it a counterexample to the fixed executor's
`FinalObservationAgreement`, `FinalLocalAgreement`, or `canonicalLocalOrder`.
Those definitions compare the executor's chosen endpoints, not every terminal
pair. The old wide/point counterexample repaired by reobservation is not used.

## Exact order field: terminal-only residual

The owner requires 「兄弟の順序によらず結果は同じになる」, including the actual
diagnostic and dictionary. No weaker language-level statement is substituted.

`source_at` and `source_steps` prove literal preservation of `state.erased.source`.
`reachable_source` recovers the source formation, ground labels, pointness, and
actual path from `initial state.erased.source root` for **every** reachable
snapshot. Thus two histories reaching the same snapshot, even under reordered
registries, have the same initial source context.

`TerminalLocalConfluence roles` asks only for Local agreement at the common
registry on two halted traces from that common ground initial source. It
requires no agreement of intermediate states, syntax of all primitive
observations, or journal ordering. The following implications are proved:

```lean
TerminalLocalConfluence roles → FinalLocalAgreement roles
TerminalLocalConfluence roles → CanonicalLocalOrder roles
```

This supplies the exact existing field domain, including execution starting
from a snapshot reachable under both registries. TerminalLocalConfluence is a
sufficient residual, not a proved confluence theorem or a necessary condition
on the particular choice executor. Fixed-snapshot registry reordering remains
the previously proved theorem.

The exact two fields left by this task are:

```lean
B4SkeletonV5.GeneratedChildren (boundary roles)
GeneralNominalCenteredAdministrativeComposition.CanonicalLocalOrder roles
```

The first follows from `UncoveredCompletion`; the second follows from
`TerminalLocalConfluence` (or the earlier exact `FinalLocalAgreement`). Neither
residual is proved. The stronger all-terminal primitive-observation route is
now ruled out, so it should not be assumed when constructing a semantic
closure proof.

## Trigger, review, and scope

No actual P/W trigger execution was added. Its earlier conditional recorded-plan
K2 theorem remains unchanged. No new owner question is introduced: the gaps
above concern the current implementation and proof interfaces, not an
unresolved language decision.

The `yulang-proofs` skill was used. The configured/callable `prover` role was
unavailable; no such agent ran. The primary constructed these bounded proofs.
Separate read-only agents reviewed production quantifiers, merge availability,
the actual terminal fork, and the final source-retention/confluence reduction.

## Validation

Commands run from `lean/`:

- `lake build Yulang.GeneralNominalCenteredTerminalAgreement` — exit 0;
  includes all six new modules and their dependencies.
- `lake build Yulang` — exit 0.
- `lake env lean Audit/CenteredTerminalProduction.lean` — exit 0;
  65 declarations audited; the dependency union is exactly `propext`,
  `Classical.choice`, and `Quot.sound`.

From the repository root, `python3 /tmp/yulang-centered-terminal-check.py` —
exit 0. This checks the frozen-file/append-only constraint, all six imports,
audit coverage, excluded proof constructs, trailing whitespace, and the
unchanged branch name. No Git references were changed.
