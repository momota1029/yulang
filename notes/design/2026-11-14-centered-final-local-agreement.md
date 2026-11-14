# Centered final Local agreement: the fixed choice executor

Status: bounded reduction, not closure of the V5 order field. This note concerns
the existing executor of the administrative centered ground boundary G′; it
does not replace that executor or alter the main statement.

The executor does not scan declarations and then pick a terminal trace.
`GeneralNominalCenteredGroundComposition.terminalState` checks eligibility and
calls `GeneralNominalCenteredGroundBoundary.finalState`. The latter is
`Classical.choose (terminal ...)`. The predicate supplied to this choice
contains the execution path, haltedness, root/child stability, and backward
model preservation. `terminal_of_accessible` proves that this predicate has a
witness. Its proof's branch order does **not** determine the value chosen by
`Classical.choose`.

Proof irrelevance removes dependence on the proofs of checkedness,
reachability, and terminal existence. It does not remove dependence on the
predicate itself. On a checked reachable input the predicate is equivalent to
just

```
Exit r s root t := Steps (Step r root) s t ∧ ∀ u, ¬ Step r root t u.
```

Pointwise equal exit predicates give equal choices. Registry reordering does
not supply that equality: installation records the literal registry in each
packet. Every packet on a reachable journal retains that registry. Consequently
a common reachable input with a recorded packet already forces the two
registries to be equal. Distinct registries can share a reachable input only
before any installation has been recorded.

This is a real distinction between the two possible arguments. The previous
Display fork proves that literal Local is not constant on a terminal set.
It does not identify which member the actual choice function selects, either
for one registry or for two reordered registries. Conversely, a bijection
between terminal sets, even one preserving semantic child inputs, does not
make classical choice commute with that bijection. Thus source inspection
alone establishes neither literal `FinalLocalAgreement` nor a concrete
counterexample for this fixed executor. In particular, this note does not
assert that the two fixed executions choose `(1,1)` and `(2,2)`.

The remaining proof obligation is restricted to distinct reordered registries,
a shared reachable packet-free input, and a transition enabled under at least
one registry. Equal registries, inputs with recorded packets, and inputs halted
under both registries are discharged independently. The new choice reduction
states this residual directly on choices from `Exit`, with no extra dependence
on accessibility or stability proofs. It is equivalent to the existing
`FinalLocalAgreement`, rather than an assumption of confluence for arbitrary
terminal traces.

The owner's requirement remains: “兄弟の順序によらず結果は同じになる”
([spec §6.3](../../spec/06-roles.md)); the accompanying text includes
pending, selected, ambiguous, rejected, and dictionary contents. The center
decision says “中心は … 具体的な型を選ぶものではない” and keeps role matching on
interval endpoints and known heads (§6.5). Neither decision specifies a
choice between extensionally equivalent descriptor revisions. No language
decision is inferred from the mathematical choice operator.

The concrete reordered pair in `GeneralNominalCenteredExitPredicates` is the
existing Display/list declaration with two children and the Display/int
declaration, in opposite orders. `inhabited_distinct_exit_predicates` proves both
registries checked, both initial reachability claims, both nonempty terminal
sets, and inequality of those sets. It uses an actual centered installation
followed by the existing terminal existence result. This disproves the
pointwise-predicate-equality shortcut, not `FinalLocalAgreement`. There is no
proved counterexample to the fixed executor and consequently no replacement
field proposed or applied this turn.

The exact new conditional result is
`GeneralNominalCenteredFixedChoice.canonicalLocalOrder_of_packet_free_choice`.
Its sole global premise is
`GeneralNominalCenteredFixedChoice.PacketFreeExitChoiceAgreement roles`, defined
in [the new module](../../lean/Yulang/GeneralNominalCenteredFixedChoice.lean).
`canonicalLocalOrder_iff_packet_free_choice` proves equivalence, not merely
sufficiency. The premise retains checkedness, registry reordering, and shared
reachability; adds registry inequality, an empty packet journal, and an enabled
step on at least one side; and compares Local at the actual classical choices
from the two exit predicates for every demand/frontier. Quantification over
existence proofs is harmless by proof irrelevance. This premise remains open.

The optional production step is
`GeneralNominalCenteredPacketFreeJoint.selected_joint_of_packet_free`:
reachability, an empty packet journal, a generated demand, and a selected Local
observation imply `Joint` for that demand/key. Its stronger frame form is
`frame_joint_of_packet_free` (reachability, empty journal, exact `Frame`).
`packet_free_trace` proves singleton raw/centered sites, empty plans/edges/aliases
after any such prefix. Thus these results cover administrative revisions, not
just the literal initial state. They do not discharge Joint after installation,
value support, or the common centered model in general `UncoveredCompletion`.

No prover role is available in this checkout/tool interface. The primary
constructs these bounded reductions, with separate read-only reviewers for
choice semantics and journal provenance. The full fixed-executor order field
and general uncovered packet completion remain open.

Validation, all from `lean/`, all exit 0:

```
lake build --wfail Yulang.GeneralNominalCenteredRegistryJournal Yulang.GeneralNominalCenteredFixedChoice Yulang.GeneralNominalCenteredExitPredicates Yulang.GeneralNominalCenteredPacketFreeJoint
lake build --wfail
lake build Yulang
lake env lean Audit/CenteredFixedChoice.lean
```

The new audit lists all 35 public theorem names and their dependencies; only
`propext`, `Classical.choice`, and `Quot.sound` occur. Independent review checked
the fixed-choice quantifiers and the distinction between differing terminal
predicates and differing Local results. No pre-existing definition was changed.
The append-only/import/audit-coverage check and `git diff --check` also exited 0.
