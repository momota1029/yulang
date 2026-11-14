# An unsettled-output refresh changes an actual centered decision

Status: **Q1 = yes**, Lean-certified from a Checked point InitialSource with an
unknown input. A source-supported resolution view leaves R pending; redirecting
one descriptor through an unsettled output makes R selected and permits an actual
centered installation. This violates the expansion deferral in
[spec §6.3](../../spec/06-roles.md) / B4 draft addendum 7. It is not merely failure
of the earlier proof interface. The investigation stops here; no frozen rule was
changed, and no nontermination claim is made.

## Source shape and controlled comparison

Schematic Yulang; the Lean declarations are the certificate, not a parser fixture:

```text
impl P[Pair[A,C]] where R[A, Out=B] { Out=Int }
impl R[Pair[Int,X]] where S[X]      { Out=X }
root: P[Pair[Pair[?u,?u],?u], Out=?u]
```

Original names are `0=Pair(1,2)`, `1=Pair(2,2)`, unknown `2=?u`, and independent
`3=Int`. Slot 3 initially lacks a cached known head. The actual first P install
forces `?u=Int` through P's output, but P's R child remains unsettled.

Two actual strict-progress refreshes start at that same reachable state. Both
expose Int at slot 3. They have **identical base data, ordinary constraints,
selected facts, sites, plans, and full model predicates**. Only the normalized
head at source 1 differs:

| Resolution view | Source 1 descriptor | R inspection reads | Actual result |
|---|---|---|---|
| Control | `Pair(2,2)` | `[1,1,2]` | `Local.pending`; no guarded R install |
| Unsettled-output refresh | `Pair(3,3)` | `[1,1,3]` | `Local.selected`; actual R install |

Every control-view head has an original-source explanation. Source 2 remains
uncached there, so the nested Int test blocks. The redirected view instead tests
the independent, source-supported Int at source 3. P's pending output is the
only available justification for connecting that Int name to source 1's children.

A concrete countermodel sets `?u=Pair(Int,Int)` and source 3 to Int. It satisfies
every original-source constraint and **every possible trusted ledger** at this
state, but falsifies `1=Pair(3,3)`. The certificate also proves P unsettled before
and after refresh. Both branches have no relevant raw, feedback, or centered
cycle; their difference is neither ordinary inconsistency nor permitted K2 use.

## Exact consumer and proposed repair

`GeneralNominalSupport.readsMany` follows the refreshed pair-child slots.
`GeneralNominalCenteredSupport.DecisionGuard` calls `ReadyAt` at those slots.
`ReadyAt` matches the identity and outer test while allowing its supporting
observation to come from a different descriptor. It accepts source 1's Pair
head from `Pair(2,2)` and source 3's independently justified Int head, without
justifying the **link** from source 1 to source 3. `Prepared` then finishes the
nested inspection; `GeneralNominalFeedbackSteps.Installable` and the actual
centered `PacketGuard` both pass. The final `.install` is constructed, not assumed.

Proposed minimal repair, **not implemented**: require trusted exact-observation
support before replacing a descriptor in the resolution cache; retain the old
supported descriptor when that proof is unavailable. Add this evidence alongside
`Refresh.exact`, covering any administrative refresh/reobservation route that
also replaces the resolution view. The evidence should concern cached `Head`
observations under source + trusted settled-output models, not demand that the
entire ordinary context satisfy those weaker models. Keep the existing full-model
certificate and provisional equations for ordinary constraints, merging, and K2;
if one cache serves both resolution and K2, separate their evidence requirements.
A final-install guard alone would block this install but could leave a previously
supported resolution view overwritten. The owner chooses the implementation.
No restored completeness or termination theorem is claimed for this proposal.

## Certificates, checks, and remaining work

Principal names in `Yulang.GeneralNominalCenteredSourceUnsettledRefreshDecision`:
`controlStep`, `control_reachable`, `identical_models`, `same_base_and_ordinary`,
`only_parent_view_changes`, `control_reads`, `control_not_decision`,
`control_local_pending`, `control_observations_source_supported`,
`control_snapshot_supported`, `refreshed_local_selected`, `no_control_install`,
`unknown_input`, and `decisive_unsettled_refresh`.
The last theorem bundles the source assumptions, both reachable refresh branches,
model equivalence, source support, P's unsettled status, absence of any trusted
redirected-head justification, different Local results, and the actual next Step.

In `Yulang.GeneralNominalCenteredSourceUnsettledRefreshWitness`, the main producer
certificates are `checked`, `initial_source`, `point`, `stepP`, `afterP_output`,
`refreshStep`, `readsR`, `centered_decisionR`, `guardR`, `stepR`,
`no_settled_afterP`, `no_settled_packet`, `centered_trusted_source_models`,
`no_trusted_redirected_head`, and `no_trusted_readbackR`. The new audit lists every
new theorem/definition, including the separate source-only Int control helper.
The decisive theorem has **no undischarged hypotheses**. Repair implementation,
new-origin production, exposures, capture reconciliation, unconditional Simulation,
and Class P accessibility remain open; the NO branch was not taken.

Final commands, from `lean/`:

```text
lake build --wfail Yulang.GeneralNominalCenteredSourceUnsettledRefreshControl Yulang.GeneralNominalCenteredSourceUnsettledRefreshWitness Yulang.GeneralNominalCenteredSourceUnsettledRefreshDecision
exit 0 (901 jobs)
lake build --wfail Yulang > /tmp/yulang-unsettled-refresh-build.log 2>&1
exit 0 (2411 jobs)
lake env lean Audit/CenteredSourceUnsettledRefresh.lean > /tmp/yulang-unsettled-refresh-audit.log 2>&1
exit 0
```

The audit checks 191 declarations; only `propext`, `Classical.choice`, and
`Quot.sound` occur. Intermediate elaboration probes returned exit 1 before their
argument-inference and dependent-record errors were fixed; final probes and
module builds returned 0. No configured/callable prover role was available;
the primary and complementary source probe produced the certificates under the
Yulang proof skill, with a separate independent review, which passed. All three module names
were checked against the entire locally available integration tree at
`122b0fabd725514c5bdcc638d539773610fcd040`; no collision or git mutation occurred.

`git diff --check` and the baseline-prefix/module-import/proof-token checks exited
0. HEAD remains `99efe22698fa7b9353440c22905ac63f83c652ed`; the only existing files
changed are the permitted aggregate imports and design index, both appended.
