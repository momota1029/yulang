# Total-materialization refresh regression and remaining successor bridges

Status: proved concrete regression; conditional progress reduction; partial canonical transport. Turn astra2-centered-23, integration input `e7003de4c`, 2026-11-15. All changes are additive. This note does not replace any target or statement.

## Source decision and actual execution

The 2026-11-15 owner instruction supplied in turn 22 requires exact cached observations to follow from source constraints, settled outputs, and justified recorded merges. The checked-out [roles §6.3](../../spec/06-roles.md) already states: 「等式そのものは捨てず、通常の制約・同じ入力の需要のまとめ・再帰型（K2）の判定には使う」 and 「未解決の出力の輪だけを根拠にする需要は、輪の外にあっても保留する」. The new regression checks the operational implementation of that decision, using the integrated [decisive source fixture](2026-11-14-centered-source-unsettled-refresh.md).

The fixture, in the same schematic type notation as its original note, is:

```text
P Pair[A,C] where R[A, Out=B] { Out=Int }
R Pair[Int,X] where S[X] { Out=X }
root: P Pair[Pair[?u,?u],?u], Out=?u
```

The source names the outer pair by 0, its first argument by 1, and the unknown `?u` by 2. Name 3 denotes Int. Installing P adds its actual total-materialization equations and creates R. P is unsettled because its R child has no packet. The full journal entails `?u = Int`; the trusted ledgers do not. The lawful control refresh caches Int at 3 and keeps the head of 1 as `Pair(2,2)`. It cannot replace that head by `Pair(3,3)`.

All regression module names below have prefix `GeneralNominalCenteredHeadMatRefreshRegression`:

| Exact theorem suffix | Established claim |
| --- | --- |
| `Source.coverage` | The existing constructor interpretation satisfies the WF coverage contract for this registry. |
| `Source.installation_model` | The new packet, current journal, snapshot effects, and enlarged live effects have the concrete common assignment `witness`. |
| `Trace.installable`, `Trace.stepP` | P is enabled and installed by the actual corrected `HeadMatStepKernel.Step`. |
| `Trace.installed_unsettled` | No recorded packet in the installed state is settled. |
| `Control.control_step`, `Control.control_trace` | An actual corrected refresh follows that installation, starting at `HeadMatStepJournal.initial context root`. |
| `Control.kept_model` | The final corrected journal is inhabited. |
| `Control.counter_cut`, `Control.kept_cut` | `sourceCounter` satisfies every trusted slice at both relevant states. |
| `Control.no_redirected_refresh`, `Control.no_redirected_refresh_kept` | Neither state has a corrected Refresh certificate for the exact redirected context. Both direct and administrative refresh require this certificate. |
| `Control.no_redirected_reobserve` | Any revision recording the same bad exact observation lacks a corrected Reobserve certificate. Its recorded-observation premise is explicit. |
| `.r_blocked`, `.r_pending` | Cached matching inspects the unknown nested pair `(2,2)`; V6 classifies R as pending. |
| `.r_not_installable`, `.no_r_packet`, `.r_generated` | Every proposed effect at R's focus is disabled, only P is presently recorded, and R is generated from the root. |
| `.decisive_regression` | A closed conjunction of checkedness, source formation, point source, WF coverage, the actual trace, inhabited final models, R pending, and both refresh exclusions. |

The counterassignment sets `?u = Pair(Int,Int)`. It satisfies the source, P's corrected **input** equations, and every possible trusted merge in this fixture. Output facts are unavailable because P is unsettled. It falsifies the proposed exact `Pair(3,3)` observation. Thus the exclusion is not an assumption about which ledger the executor might choose: it quantifies over all trusted ledgers.

There are two important limits. First, the root contains unknown `?u`: the theorem establishes a checked, source-formed, WF, point-source kernel trace, **not** `B4TargetV6.Reachable` for the ground boundary, whose Initial also requires `GroundRoots`. Second, R pending is proved at the concrete control endpoint; no assertion about every possible future trace is made. A later independent settled justification may legitimately resume it.

`GeneralNominalCenteredHeadMatPairCycles.acyclic` rules out the corrected semantic K2 cycles used in the fixture. Its hypotheses are one corrected journal model and a finite scalar/pair tree at every source identity in that model. `Trace.witness_trees` and `Control.kept_model` supply them. This is not an exhaustive K2 theorem for all total expressions.

`Trace.packet_legacy` is a fixture-specific bridge used to reuse its ordinary-constraint certificate. It follows from P's explicit Int equation and the fixture's input equations. No general erasure of corrected packet models into legacy models is assumed.

## Progress: proved measure, open finite producer

`GeneralNominalCenteredHeadMatStepMonotonicity` proves raw-model restriction, cached-known and descriptor-point monotonicity, edge growth, and semantic commitment preservation for the actual successor constructors. In particular, RawEqual uses raw-model restriction; corrected semantic commitments use `HeadMatStepJournal.Models` restriction. These are different premises and are not interchanged.

`GeneralNominalCenteredHeadMatStepFiniteProgress` reuses the generic finite-fact measure with **new** `Represents` and `Holds`. Its signature delta means the corrected `HeadMatStepPackets.Inputs` and `Outputs`, not the old packet equations. `fresh_fact` handles installation, both refresh forms, merges, equality feedback, and reobservation. Enqueue is excluded by the actual trace's registration invariant.

The exact results are:

```lean
accessible_of_cover
  (cover : FiniteCover registry root (initial context root)) :
  Acc (fun next current => Step registry root current next) (initial context root)

progress (covers : GroundCover roles) :
  GeneralNominalCenteredHeadMatStepExecutor.Progress roles
```

`GroundCover` remains undischarged. It quantifies over checked registries and contexts with `InitialSource`, point arguments, `GroundRoots`, and WF `Coverage`. It must produce finite lists of semantic signatures, source identities, and occurrences that cover **every future reachable enabled novel installation**, every source/slot, and every recorded centered site. The measure theorem alone does not construct these lists.

The retrospective producer now has two concrete new ingredients:

- `GeneralNominalCenteredHeadMatStepHeadMatching.plan_matching` and `.capture_descent` use a head-only Frame, unchanged constructors and interpretation, nonempty where requirements, one corrected packet model, and finite input labels (`GroundAccessibility.Inputs`). They produce centered capture meanings and strict Paterson mass decrease for every normalized where argument list. They do not assume legacy output schemas or whole legacy models.
- `GeneralNominalCenteredHeadMatStepChildReadback.argument_value` reads the total child equation for any successfully translated argument. `.variable_argument` identifies a syntactically variable child's center with its binder; `.variable_meaning` transports the capture's closed meaning to that center under `Ready`.

The remaining producer link is general compound-child closed readback: derive `GroundAccessibility.Inputs` at every emitted child from the corrected total equations and the chosen capture meanings. It must handle source normalization and all checked compound arguments, and then feed the retrospective depth/finite-signature enumeration. The variable theorem is not this general producer.

## Canonical transport: fixed-context packet semantics

`GeneralNominalCenteredHeadMatStepPacketReordering` proves:

- `variables_rebase`, `requests_rebase`, `emitted_schema`, and `child_schema`: exact equality of compiler inputs and total schemas when the registry and declaration are rebased by `Reorders`/`DeclarationReorders`;
- `inputs`, `outputs`, and `holds`: equivalence of the corrected packet semantics under that rebasing.

No extra role-equality or output-consistency premise is needed for these packet results; the checked declaration is already part of the Plan. Class-default effects are handled by the preceding `HeadMatStepOrder.ready` and `.class_effects` results.

These theorems keep the observation context fixed. They do not yet construct the corresponding current context after installations, rebase stored snapshots/effects, transport trusted input/output/merge ledgers, or simulate complete successor Steps. Consequently the exact prior residual remains:

```lean
GeneralNominalCenteredHeadMatStepExecutor.CanonicalExitLifting roles
```

This requires an original-registry terminal trace whose Local at the canonical registry agrees with the chosen canonical terminal, for every demand and frontier, from every checked reachable packet-free input. Fixed-state Local invariance and fixed-context packet invariance do not establish this statement.

## Availability, K2, and law status

The remaining availability premise is unchanged:

```lean
GeneralNominalCenteredHeadMatStepAvailability.Extension state effect :=
  GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet ∧
    ∃ model, GeneralNominalCenteredHeadMatStepJournal.InstallationModels state effect model
```

The common model must satisfy the corrected current journal, new packet equations, chosen effects, and the enlarged live obligations of both the new and every previous effect. The fixture supplies one such model but does not discharge general allocation coherence, independence, value support, or journal-preserving extension. The preceding selected-effects theorem still requires its positive inhabited `ChosenHead` baseline. `SelectedCompletion roles`, and thus general `GeneratedSelectedChildren roles`, remain open.

The existing Test/Origin vocabulary still lacks general open-tail and multi-tag payload projection coverage. The pair-model acyclicity lemma does not remove that implementation/proof obligation. No new WF reachable stable failure is certified, and no new semantic question is raised.

The corrected boundary therefore retains its nine unconditional law shapes from [the preceding note](2026-11-15-centered-head-mat-trusted-cache.md). `Progress` and executor halting remain conditional; `CanonicalLocalOrder` remains conditional on `CanonicalExitLifting`. Exact remains unconditional; SaturationTotal requires Progress; OrderIndependent requires CanonicalExitLifting. No complete V6 Statement or EvidenceNode result is claimed here.

## Verification and review

The new audit `lean/Audit/GeneralNominalCenteredHeadMatRefreshRegression.lean` lists every new public theorem by fully qualified name. The primary constructed these bounded proofs; the configured environment supplies no prover launch surface. An independent reviewer checked both the regression and the five bridge modules and ran direct Lean checks. No prover agent ran.

All 85 new public theorems passed the dependency audit; the dependency union is exactly `propext`, `Classical.choice`, and `Quot.sound`. The final commands below exited **0**. Intermediate elaboration failures were corrected before these checks.

```sh
# Working directory: lean; exit 0 (covers all ten new modules)
lake build --wfail Yulang.GeneralNominalCenteredHeadMatRefreshRegression Yulang.GeneralNominalCenteredHeadMatStepFiniteProgress Yulang.GeneralNominalCenteredHeadMatStepChildReadback Yulang.GeneralNominalCenteredHeadMatStepPacketReordering > /tmp/centered23-modules-build.log 2>&1

# Working directory: lean; exit 0
lake build --wfail Yulang > /tmp/centered23-build.log 2>&1

# Working directory: lean; exit 0
lake build --wfail > /tmp/centered23-default-build.log 2>&1

# Working directory: lean; exit 0
lake env lean Audit/GeneralNominalCenteredHeadMatRefreshRegression.lean > /tmp/centered23-audit.log 2>&1

# Working directory: repository root; exit 0
git diff --check
```

The append-only/import/proof-token check and the dependency-set parser also exited 0. The only edited pre-existing files are `lean/Yulang.lean` and `notes/design/INDEX.md`; each retains its HEAD contents as an exact byte prefix. All ten new modules are imported. The branch remains `astra2/centered`, HEAD `e7003de4cf4735c7211047ec38ba016455c11a8e`. No references were changed. No frozen target, prior module, other worker's file, aggregate audit, lake configuration, spec, or README was edited.
