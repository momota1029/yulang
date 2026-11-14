# Centered canonical executor

Draft, 2026-11-14. G′ and the V5 statement are frozen. A new executor is an
implementation parameter, not a change to the language's order requirement.

`B4SkeletonV5.B4Bridges` has four fields that mention the executor:

| Field | Required registry and transport |
| --- | --- |
| `execution` | `Steps (Step r root) s (run r s root).1`. Canonical execution must be lifted back to an actual trace from the original `s` under **r**. |
| `halted` | No `Step r root` leaves that returned state. Reflect an enabled original action to the canonical state. |
| `treeExecution` | Resolve `frontiers roles r` at the returned original state. Compute the diagnostic there; the existing exact-diagnostic theorem applies directly. |
| `canonicalLocalOrder` | Compare `Local r` and `Local r'` at their respective returned states for every demand/frontier. Both returned observations must agree with the same canonical execution. |

The other ten fields do not mention the executor: `progress`, `closure`,
`stepModels`, `frontierLocal`, `localIdentity`, `whereAccessible`,
`dictionaryRefl`, `evidenceNode`, `generatedChildren`, and `initialReorders`.
Eight are already proved for G′; the last two semantic obligations remain
`B4SkeletonV5.EvidenceNode (boundary roles)` and
`B4SkeletonV5.GeneratedChildren (boundary roles)`.

Route A uses a fixed representative of the entire `Reorders` equivalence
class. This includes both visible declaration order and where-clause order.
Choice is made from extensionally equal equivalence-class predicates, so
reordered inputs produce literally equal representatives. It does not choose
separately from registry-dependent sets of terminal states.

Packets carry the literal registry. A canonical final state therefore cannot
simply be returned as an original execution. For a general reachable input,
normalize its historical packets/plans as well, or handle inputs with packets
separately: shared reachable inputs under different registries are packet-free
by `GeneralNominalCenteredRegistryJournal.distinct_shared_packet_free`.

Retagging just `packet.registry` is insufficient. A changed where order also
changes the stored declaration. `privateState` retains reservation/ownership
lists in registry order; `Plan.emitted` retains where order. The intended
simulation preserves actual descriptors, source identities, models, generated
edges, and Local, while relating those administrative lists by permutation.
It must extend through historical packet contexts and trusted support facts.
Existing fixed-context candidate reordering proves equal canonical children
and equivalent branch constraints, but does not yet prove this state transport.

No prover role is registered in the checkout/tool interface. The primary
constructs bounded proofs with separate read-only source and counterexample
reviewers.

The implementation retains the old executor on nonempty journals. On an empty
journal it chooses an original-registry terminal satisfying `LiftedExit`: its
Local observations at `canonical r` equal those of the fixed canonical run.
When no such terminal exists, it falls back to the old executor. Consequently
original execution and haltedness hold independently of the transport proof.
Any choice among lifted exits is safe for order agreement because each has
the prescribed canonical observations. There is no choice-equivariance premise.

Proved results (namespace prefixes are the module names under `Yulang`):

| Module | Main exact theorem names and scope |
| --- | --- |
| `GeneralCanonicalRegistry` | `canonical_eq`, `canonical_eq_iff`, `canonical_checked`, `canonical_idempotent`: full visible/where classes, including unchecked registries for invariance. |
| `GeneralNominalCenteredRegistryPassive` | `packet_free_steps`, `packet_free_reachable`, `canonical_reachable`: actual unchanged states and traces before installation. |
| `GeneralNominalPacketReordering` | `holds`, `inputs`, `outputs`, `shared_emitted_sites`: fixed-context rebasing preserves branch semantics, both origin-choice predicates/values, and literal raw child sites. |
| `GeneralNominalCenteredPlanReordering` | `equations`, `holds`, `emitted_perm`, `tests_mem`, `installed_models`, `installed_raw_sites`, `installed_edges`, `installed_center_sites`: centers and full equations survive; the installation results compare syntactic installs into the same predecessor. |
| `GeneralNominalCenteredCanonicalExecutor` | `execution`, `halted`, `treeExecution`, `final_models`, `final_stable`: unconditional on the existing checked/reachable domain. `canonicalLocalOrder`, `bridges`, `composition`: conditional as stated below. |
| `GeneralNominalCenteredCanonicalTransport` | `steps_backward`, `halt_reflects`, `lifted_exit_of_simulation`, `canonical_exit_lifting`, `canonicalLocalOrder`, `composition`: a concrete bidirectional simulation would close the order obligation. |

Status: **eleven unconditional fields, not twelve**. The unresolved order
premise is exactly
`GeneralNominalCenteredCanonicalExecutor.CanonicalExitLifting roles`:

```
∀ r, Checked r → ∀ s root, Reachable G′ r root s → s.erased.current.packets = [] →
  ∃ t, Steps (Step r root) s t ∧ (∀ u, ¬ Step r root t u) ∧
    ∀ d f, Local (canonical r) t d f ↔
      Local (canonical r) (terminalState (canonical r) s root) d f.
```

`GeneralNominalCenteredCanonicalTransport.ReachablePermutationSimulation roles`
is a sufficient alternative: for each such input there is a relation containing
`(s,s)`, matching **actual** centered steps in both directions between `r` and
`canonical r`, and preserving `Local (canonical r)` for every demand/frontier.
This relation has not been constructed. The packet/plan lemmas do not prove
`PacketGuard`, `Installable`, support-slice or `Trusted` correspondence between
unequal historical/current contexts. Those state/ledger congruences are the
remaining implementation work; no frozen V5 field was found incompatible with
the transport. Route A remains viable, so Route B was not used.

The complete composition has three undischarged global premises, precisely
the fields of `GeneralNominalCenteredCanonicalExecutor.Remaining roles`:
`canonicalExitLifting`, `evidenceNode : B4SkeletonV5.EvidenceNode (boundary roles)`,
and `generatedChildren : B4SkeletonV5.GeneratedChildren (boundary roles)`.
The transport module's composition replaces the first by
`ReachablePermutationSimulation roles`; it does not add both premises.
Packet/plan rebasing additionally states its ordinary local premises explicitly:
registry/declaration reorder proofs, the role equality where needed, and the
historical/current context equality for `installed_models`. These are not
assumptions silently discharged by source reachability.

Validation, from `lean/`, all exit 0:

```
lake build --wfail Yulang.GeneralCanonicalRegistry Yulang.GeneralNominalCenteredRegistryPassive Yulang.GeneralNominalPacketReordering Yulang.GeneralNominalCenteredPlanReordering Yulang.GeneralNominalCenteredCanonicalExecutor Yulang.GeneralNominalCenteredCanonicalTransport
lake build --wfail
lake build Yulang
lake env lean Audit/CenteredCanonicalExecutor.lean
```

The new audit lists all 73 public theorem names and reports only `propext`,
`Classical.choice`, and `Quot.sound`. Independent review checked the quantifiers,
the two emitter choices, and the limits of the fixed-context installation
results. G′, the prior executor, and both V5 files remain unchanged.
The append-only/import/audit-coverage check and `git diff --check` also exited 0.
