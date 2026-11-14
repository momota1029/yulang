# Centered source retention and the selected-ledger readback obstruction

Status: strengthened coverage, its initializer and transport are proved. A
second concrete quantifier obstruction refutes the exact selected-ledger
`InputReadbackAndOrigins'` stage. Unconditional centered `Simulation`,
`ClassPSourceProduction`, and Class P accessibility remain open. Proof search
stopped when the counterexample compiled, as requested. This does not refute
`NonterminalInstallPreservation'` itself, an existential ledger-extension
variant, or termination of the actual transition relation.

All new module names start with `GeneralNominalCenteredSource`. No previous-cycle
module, transition, boundary, target, or frozen document was changed. Only new
imports and this index entry were appended to the two allowed existing files.

## Strengthened coverage

`GeneralNominalCenteredSourceLiveReadbacks.Coverage'` extends the previous
`Coverage` with `Retention`. For an original source identity, `FutureRead`
means that some finite actual centered transition suffix reaches a state with
an inhabited model predicate and a relevant origin equal to that identity in
all its full models. Relevant origins are registered site centers and the
input/capture/binder origins of installable plans at registered sites.

For each such original identity, `Retention` supplies a source-labelled finite
`Value`, with the fixed source vocabulary, under the selected centered ledger.
Only the leaves of that current value are live source holes. Every such leaf
belongs to `inventory.holes` (`Retention.live_mem`); in particular, an opaque
source presentation keeps its index (`Retention.opaque_mem`). This allows a
justified constructor exposure to replace a previously opaque index instead of
requiring that index to survive forever. It does not require values for source
identities that no current or future use can read. The finite suffix predicate
assumes neither accessibility nor a simulation. Inhabitation prevents vacuous
aliases in inconsistent full-model predicates.

`initialized` proves the invariant at the full-frontier initializer for every
`InitialSource` and `PointSource`. `Retention.full` also supplies the retention
component at any state when all original frontier holes remain.

`GeneralNominalCenteredSourceLiveChecks.counterexample_inventory_excluded`
excludes the previous turn's small inventory for **every** journal and selected
trusted ledger, using the same real source witness. `old_job_excluded` checks
the exact earlier bundled installation. `full_frontier_initialized` checks the
concrete example with the intended full-frontier initializer.

## Preservation proved

`Retention.step` preserves the new property through every centered `Step`,
including nonterminal installation: future uses before a step include future
uses after it, and the unchanged selected ledger has the same coarse models.
This theorem preserves the retention component; it does not construct new site
labels required by the complete `Coverage'` after a nonterminal installation.

`GeneralNominalCenteredSourceLiveTransport` proves complete strengthened
coverage transport for `administrative`, `refresh`, `merge`, and
`terminal_install`. Administrative transport covers the raw refresh, equation,
and reobservation operations. Merge transport retains both sites’ existing labels and their meanings under
the unchanged selected coarse ledger; it does not prove syntactic equality of
the two labels.

`Retention.replace`, `Retention.eliminated_not_live`, `Coverage'.replace`, and
`eliminate` transport all selected meanings through a semantically justified
simultaneous replacement. A removed index is not live **after** replacement;
it may have been a live opaque index before exposure. `Replacements.transport`
handles finite sequences of such replacements. A bare syntactic `Trace` does
not supply the semantic replacement readback. The new `Replacements` relation
records that readback explicitly, together with scope, vocabulary, and bounds.
Replacement can reset the auxiliary raw selected ledger to empty while retaining
the centered ledger; it changes no runtime fact or state.

`GeneralNominalCenteredSourceLiveConstruction` defines the strengthened exact
remaining case `NonterminalInstallPreservation'`. Its `next` exhausts all real
Step constructors, with only that case as its source-production premise.
`simulation`, `accessible`, and `class_p_source_production` carry this premise
explicitly to the existing centered journal reduction.

## Source production proved and remaining statements

`GeneralNominalCenteredSourceLiveProduction` defines `OriginFrame'`, retaining
source meanings alongside the old source frame. The proved statements are:

- `original_input`: a directly named **original** source in the plan inputs has
  a labelled value, using the real guard's model witness and retention. It does
  not cover arbitrary fresh binders or projections by itself.
- `frame_of_input`: exact selected-ledger snapshot readback and new input-origin
  values produce a trusted input frame with retention.
- `finish`: `CommonCaptures` produces the final journal and complete strengthened
  coverage; child labels use the same explicit-center captures.
- `nonterminal_install_of_three`: the three independently named strengthened
  stages imply `NonterminalInstallPreservation'`.

Every remaining universal source premise is explicit:

1. `InputReadbackAndOrigins'`: for every real bundled installation with retention,
   the **already selected** ledger validates its exact cached report, and the
   ledger extended by that input covers its new input origins. This statement
   is false, by the counterexample below.
2. `FullReportExposures'`: from a retained input frame, global replacements produce
   an individually matching frame with the precisely transformed old labels.
   No unconditional constructor-expansion/K2 production theorem is established.
3. `CaptureReconciliation'`: from an individually matching retained frame, global
   replacements produce `CommonCaptures`, including historical agreement.
   No unconditional common-capture production theorem is established.
4. `NonterminalInstallPreservation'`: the full remaining installation case is
   still open; the failed sufficient input stage does not establish its negation.
5. `ClassPInstallPreservation'`: the universal Checked/InitialSource/PointSource
   version of that remaining case, required by `class_p_source_production`, is
   still open.

`frame_of_input` retains its exact readback and new-origin arguments; `finish`
retains `CommonCaptures`; replacement transport retains its semantic replacement
values, vocabulary and bounds. None of these producer premises is silently
obtained from retention, full-model soundness, or inconsistent coarse models.

## Concrete second counterexample

The checked source shape is schematic Yulang, not a parser fixture:

```text
impl P[Pair[A, C]] where R[A, Out = B] { Out = B }
impl R[Pair[X, Y]] where S[X]         { Out = X }

root demand: P[Pair[Pair[?u, ?u], ?u], Out = ?u]
```

The initial source has `0 = Pair(1,2)`, `1 = Pair(2,2)`, and unknown `2 = ?u`.
An independent source slot `3` has ordinary type `Int`, initially without a cached
known head. The first installation emits an R site with explicit center `1`.
Its fresh output center `b` is constrained by the full P output equations to
be equal to `?u`.

A real centered refresh caches center `1` as `Pair(b,b)` using a new slot naming
`b`. The full-model refresh certificate is proved. The refresh also exposes
`Int` at slot `3`, supplying strict known-source progress. R then installs through
the actual centered constructor. Its readiness uses the original same-shape
observation `1 = Pair(?u,?u)`. All source selection, novelty, raw and centered
cycle exclusions, alternatives safety and consistency witnesses are proved;
no step or installation guard is a theorem parameter.

At this reachable refreshed state, `LiveStart` supplies:

- every original frontier hole, a valid inventory and a historical P journal;
- root label `Pair(leaf 1, leaf 2)` and the emitted R label `leaf 1`;
- empty selected raw and centered ledgers, complete site coverage, and retention.

The runtime state is actually reachable. The particular `LiveStart` journal and
inventory are witnesses at that state; no semantic refinement history from the
initializer to this particular auxiliary pair is proved. The stage quantifies
over every such journal and inventory with coverage, so this is sufficient to
refute it. It does not assert that the intended source-production trajectory
selects this pair.

The empty centered ledger is trusted. Its coarse models retain the original
source and root centers, but do not include P's output equation. The countermodel
sets `?u = Int` and the fresh `b = Pair(Int,Int)`, preserving all original sources.
It therefore invalidates the exact refreshed observation `1 = Pair(b,b)`.
Explicit center `1` and its original labelled value are present throughout;
there is no missing-center or lost-provenance argument.

In namespace `Yulang.GeneralNominalCenteredSourceRefreshWitness`:
`checked`, `initial_source`, `point`, `stepP`, `refreshStep`,
`refreshed_reachable`, `enabledR`, `guardR`, `stepR`, and
`no_empty_readbackR` certify the runtime side of the example.

In namespace `Yulang.GeneralNominalCenteredSourceRefreshObstruction`:
`liveStart_exists`, `not_input_readback_and_origins`, `unknown_input`, and
`strengthened_counterexample` certify the full-frontier strengthened invariant
and the negative selected-ledger claim. The last theorem includes the valid
inventory, all original holes, actual trace and actual next step.

This establishes a contract/quantifier obstruction. It does not show a source
program diverges, nor that all possible trusted ledger extensions fail. No
language-owner question is raised. The next proof contract must address exact
snapshot support rather than infer it merely from source-hole retention.

## Checks and scope

All final commands were run from `lean/`:

```text
lake build --wfail Yulang.GeneralNominalCenteredSourceLiveReadbacks Yulang.GeneralNominalCenteredSourceLiveChecks Yulang.GeneralNominalCenteredSourceLiveTransport Yulang.GeneralNominalCenteredSourceLiveConstruction Yulang.GeneralNominalCenteredSourceLiveProduction Yulang.GeneralNominalCenteredSourceRefreshWitness Yulang.GeneralNominalCenteredSourceRefreshObstruction
exit 0 (900 jobs)

lake build --wfail Yulang
exit 0 (2406 jobs)

lake env lean Audit/CenteredSourceLiveRetention.lean > /tmp/yulang-source-live-retention-audit.log 2>&1
exit 0
```

The new audit checks all 208 new theorem/definition declarations. Its dependency
sets contain only `propext`, `Classical.choice`, and `Quot.sound`. No proof escape
was used. Intermediate Lean elaboration probes in `/tmp` had exit 1 while being
repaired; the final fixture and composed counterexample each compiled with exit
0. One build invocation from the repository root instead of `lean/` exited 1
because no Lake configuration exists there:
`lake build --wfail Yulang.GeneralNominalCenteredSourceRefreshWitness Yulang.GeneralNominalCenteredSourceRefreshObstruction`.
The identical command rerun from `lean/` exited 0 (897 jobs).

The local `integration/m1-final` branch name was absent (read command exit 128).
Module names were checked against the entire locally available
`refs/remotes/origin/integration/m1-final` tree at
`122b0fabd725514c5bdcc638d539773610fcd040` (tree read exit 0), with no collisions.
No network update or git reference mutation was performed.

The Yulang proof skill was applied. No configured or callable `prover` role
was available; no prover agent is claimed. The primary constructed the invariant,
transport, conditional producer and journal obstruction. A separate source probe
constructed the concrete guarded trace, and a separate reviewer checked the
contract scope and new proofs. The final independent review passed and checked
that auxiliary-journal reachability is not claimed. Kernel compilation and dependency audit certify
the reported mathematical statements; they do not certify the still-open
unconditional accessibility claim.

`git diff --check` exited 0. A baseline-prefix and HEAD check exited 0:
only `lean/Yulang.lean` and `notes/design/INDEX.md` changed among previously
tracked files, both by appending; all seven new modules are imported, and HEAD
remains `c84b51cf25d27717e31405b723ba5947bb86c6a5`.

## Exact theorem inventory

The following are theorem declarations; the audit also checks the supporting
value and transport definitions. Each group gives its full namespace.

`Yulang.GeneralNominalCenteredSourceLiveReadbacks`:

- `FutureRead.before`
- `FutureRead.site`
- `FutureRead.candidate`
- `Retention.live_mem`
- `Retention.opaque_mem`
- `initialized`
- `Retention.eliminated_not_live`

`Yulang.GeneralNominalCenteredSourceLiveChecks`:

- `future_child`
- `source_member`
- `counterexample_inventory_excluded`
- `old_job_excluded`
- `full_frontier_initialized`

`Yulang.GeneralNominalCenteredSourceLiveTransport`:

- `administrative`
- `refresh`
- `merge`
- `terminal_install`
- `eliminate`
- `Replacements.changes`
- `Replacements.transport`

`Yulang.GeneralNominalCenteredSourceLiveConstruction`:

- `retained_next`
- `next`
- `simulation`
- `accessible`
- `class_p_source_production`

`Yulang.GeneralNominalCenteredSourceLiveProduction`:

- `original_input`
- `frame_of_input`
- `finish`
- `nonterminal_install_of_three`

`Yulang.GeneralNominalCenteredSourceRefreshWitness`:

- `p_checked`
- `r_checked`
- `checked`
- `initial_source`
- `point`
- `queriesP`
- `reportP_exact`
- `bindingsP`
- `p_sorted`
- `schemaP_exact`
- `inputSchemaP_exact`
- `witness_source`
- `projectionP`
- `ordinaryP`
- `inputsP`
- `outputP_large`
- `witness_output`
- `outputsP`
- `packetP_holds`
- `locatedP`
- `preparedP`
- `witness_no_nominal`
- `feedback_acyclic`
- `raw_acyclic`
- `no_legacy`
- `source_smaller`
- `source_no_raw`
- `initial_no_feedback`
- `no_rootP`
- `no_candidateP`
- `rootP_ready`
- `p_only`
- `survivorP`
- `selectedP`
- `enabledP`
- `headSchemaP_exact`
- `binderP_zero`
- `binderP_one`
- `binderP_two`
- `headSchemaP_holds`
- `inputSchemaP_holds`
- `childP_center`
- `childP_arguments`
- `childP_schema`
- `childrenP_holds`
- `binderP_fits`
- `centered_inputsP`
- `namedSchemaP_holds`
- `planP_holds`
- `readsP`
- `source_headP`
- `source_readyP`
- `source_guardP`
- `centered_decisionP`
- `initial_no_cyclic`
- `inspectionP_count`
- `safeP`
- `alternativesP`
- `guardP`
- `novelP`
- `stepP`
- `refresh_source_embed`
- `refresh_raw_known`
- `refresh_view_known`
- `outputP_supported`
- `refreshed_support`
- `afterP_output`
- `refreshed_exact`
- `progress_unknown`
- `progress_known`
- `refreshStep`
- `refreshed_reachable`
- `queriesR`
- `reportR_exact`
- `bindingsR`
- `r_sorted`
- `locatedR`
- `readsR`
- `current_headR`
- `old_headR`
- `readyR`
- `bad_old`
- `bad_source`
- `bad_coarse`
- `current_headR_not_source`
- `no_empty_readbackR`
- `rootR_outputs`
- `schemaR_exact`
- `inputSchemaR_exact`
- `projectionR`
- `ordinaryR`
- `inputsR`
- `outputsR`
- `witness_afterP`
- `witness_refreshed`
- `packetR_holds`
- `privateP_ordinary`
- `freshR`
- `linkedR`
- `preparedR`
- `refreshed_smaller`
- `refreshed_no_raw`
- `refreshed_no_feedback`
- `no_rootR`
- `no_candidateR`
- `rootR_ready`
- `r_only`
- `survivorR`
- `selectedR`
- `refreshed_alias_eq`
- `child_identity_not_root`
- `childrenP_exact`
- `refreshed_sites`
- `compatibleR`
- `mergesClosedR`
- `feedbackMergesClosedR`
- `jointR`
- `enabledR`
- `headSchemaR_exact`
- `binderR_zero`
- `binderR_one`
- `headSchemaR_holds`
- `inputSchemaR_holds`
- `childR_center`
- `childR_arguments`
- `childR_schema`
- `childrenR_holds`
- `binderR_fits`
- `centered_inputsR`
- `namedSchemaR_holds`
- `planR_holds`
- `graph_tests_refreshed`
- `pair_child_not_root`
- `graph_acyclic_refreshed`
- `refreshed_no_cyclic`
- `source_guardR`
- `centered_decisionR`
- `inspectionR_count`
- `safeR`
- `alternativesR`
- `centered_child_registered`
- `guardR`
- `novelR`
- `generatedR`
- `stepR`

`Yulang.GeneralNominalCenteredSourceRefreshObstruction`:

- `root_label`
- `root_allowed`
- `root_readback`
- `root_vocabulary`
- `child_identity`
- `liveStart_exists`
- `not_input_readback_and_origins`
- `unknown_input`
- `strengthened_counterexample`

