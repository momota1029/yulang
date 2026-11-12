# Item 4i: downstream output support and the remaining installation bound

Status: **Partial implementation and checked reductions; termination remains open.**
Date: 2026-11-13. Baseline: `d5a79a7bf`.
Authority: [spec §6.3](../../spec/06-roles.md),
[B4 draft addendum 6](2026-11-08-b4-main-statement-draft.md), and the owner answer
at the end of the [termination plan](2026-11-13-termination-proof-plan.md).
No new language decision is proposed.

## Scope and independent definition

The new boundary is `GeneralNominalDownstreamBoundary.boundary roles`. It uses
the existing general registry, nominal context, occurrence identities, journal,
packet equations, allocation, and dictionary evidence. Existing definitions are
unchanged. `GeneralNominalDownstreamSteps.Step` is a subrelation of
`GeneralNominalSupportSteps.Step`; only installation receives an additional
condition. Merges, ordinary equality feedback, refresh, and descriptor
replacement retain their old transitions and full model sets.

The owner chose downstream deferral, not declaration rejection and not a rule
that every provisional producer must already be discharged. The implementation
uses the following executor-independent predicates in
[GeneralNominalDownstreamSupport](../../lean/Yulang/GeneralNominalDownstreamSupport.lean):

- `Available state identity test` is the existing `HeadSupported` predicate with
  every stored dependency enabled. `pool_exact` proves that its model slice is
  exactly `AllModels`. Named output/merge equations participate unchanged.
- `Need registry state occurrence identity test` includes every unnamed lower
  input and positions actually read by a visible non-variable candidate in a
  certified observation view. A head must be journal-certifiable. Thus a blocked,
  uninstalled child is included, and withholding its refresh cannot hide an
  output cycle. Variable capture does not inspect a nominal argument's head.
- `Waiting` traverses recorded child edges and registered aliases through
  unresolved obligations only. A discharged intermediate cuts the path.
  Alias traversal is equality, not an extra strict support edge. The original
  `Generated` remains the complete diagnostic generation relation.
- `Grounded registry state producer` is inductive. A discharged producer is a
  leaf. Otherwise each needed head of an unresolved waiting descendant must
  have a chosen finite support whose producers are themselves Grounded.
  These supports are existential alternatives. No union of all possible
  explanations is used. A genuinely unknown child contributes no known-head
  dependency.
- `Supported` requires Grounded for the selected support list. The new packet
  guard is the old guard conjoined with Supported. The boundary's decision guard
  uses the same condition; lack of a supported decision is inspection pending.
  Root/candidate K2 still precede that pending case.

`HeadSupported` continues to allow a broader descriptor with the same head
`Test`; it does not demand the exact cached child intervals. `View` includes arbitrary finite sequences of existing certified refresh and
descriptor replacement, preserving full journal models (`view_models`). Thus
reobservation-only nested reads are covered as well as ordinary refresh reads.
The tests and
normalization equivalences are the existing general ones. This addition does
not introduce a new normalization procedure or inspect nominal bodies.

Discharged outputs, independent source heads, and alternative provisional
explanations can resume consumers. The support ledger is not erased when a
proof becomes unavailable. The existing insertion-time alternative retention
is reused; general rejustification completeness remains a separate obligation.

An independent review found a concrete definition-level risk in using all
`Generated` descendants: historical edges beyond a discharged intermediate can
remain present after reinstallations or alias merges. That would inspect an
already discharged branch. `Waiting` fixes this implementation issue; no
owner question is needed. `waiting_open` and `alias_grounded` prove the relevant
cut and alias behavior.

## New proof contribution toward L5

[GeneralNominalDownstreamDepth](../../lean/Yulang/GeneralNominalDownstreamDepth.lean)
proves that the inductive support certificate has a finite natural depth at each
fixed snapshot. This is nontrivial because `Need` quantifies over potentially
infinitely many certified observation contexts.

The proof restricts each selected support to the finite `dependencyPool`.
`slice_restrict` preserves every semantic head claim. Among pool members used
by at least one explanation, the induction hypotheses give finitely many
depths; their maximum works for all required heads at this snapshot. Conversely,
a finite-depth certificate yields Grounded. A further finite maximum covers
all Grounded producers recorded in this journal.

The exact statements are:

```lean
Grounded registry state producer ↔
  ∃ depth, GeneralNominalDownstreamDepth.AtDepth registry state depth producer

∃ depth, ∀ producer ∈ GeneralNominalSupportChoices.dependencyPool state,
  Grounded registry state producer →
  GeneralNominalDownstreamDepth.AtDepth registry state depth producer
```

This does **not** construct the installation measure. The pool and its maximum
can change with a new packet. A merge can change the waiting cone; new output
facts can create new needed heads. No theorem says the chosen depth decreases
or stays within an initial-source bound. Using the current maximum directly as
a rank would omit exactly that missing update lemma.

The modelwise alternative is still invalid: `no_modelwise_rank` transports the
existing output-growth countermodel to a first installation permitted by this
new guard. Thus neither arbitrary-model argument size nor merely having a
finite snapshot support depth supplies L5. This is a measure obstruction, not
a new infinite execution or a new semantic question.

## Regression scope

| Example | Kernel-checked result in this item | Limit |
|---|---|---|
| Display(list int) | Actual new Step installation, exact list declaration and `[Display int]` child | Inherits existing general nominal fixture |
| Wrap(list int) | Actual new Step installation, exact Container child and item equation | Inherits existing general nominal fixture |
| Container in the P sibling fixture | Empty/source support satisfies the new packet guard after P's actual first installation | Full leaf `Installable`/novelty and installation trace are not supplied here |
| Direct R output growth | Actual first installation and refresh remain SourceFormed; recursive child is blocked and Local pending | Uses existing K2-safe regression |
| Redundant sibling supports (4g) | Both unresolved siblings are Grounded despite the old permitted-edge cycle | Source-conservative P installation supplies independent explanations |
| Wrap/Container/P downstream chain | Concrete inhabited, exact-model journal; Wrap capture/child identities; cut-model necessity; exclusion of the first P/W decisions at source 2 | The complete P,C,W SourceFormed prefix is not yet constructed; see certificate below |

The last regression uses
[GeneralNominalDownstreamSiblingFixture](../../lean/Yulang/GeneralNominalDownstreamSiblingFixture.lean).
Its `PrefixCertificate state` exposes, rather than assumes silently, the facts
needed at the first downstream expansion: the original source context,
unresolved Wrap and its Container child, their unresolved waiting path, the
journal-certified list head at source 2, and a finite separating model for all
facts not depending on Wrap. From that cut, every explanation of the new head
must contain Wrap. The child's explanation would therefore return to Wrap,
contradicting Grounded. A downstream consumer need not be in this cycle.

`cut_journal_certificate` constructs this certificate for the concrete
`cutJournal`, rather than leaving it uninhabited. `cut_journal_exact` proves
that its full journal Models agree with its retained fact ledger, and
`cut_journal_models` supplies a finite model, and
`cut_journal_no_feedback_cycle` excludes every entailed type cycle. The
exclusion therefore follows from output support, not an inconsistent journal
or a K2 rejection. `concrete_wrap_not_grounded` and
`concrete_downstream_head_blocked` have no prefix premise. This journal uses
actual declaration/capture/emission identities, but it is not asserted to be
the actual sequence of transition results.

The complete real transition prefix additionally needs post-installation
capture freshness, joint applicability, exact alternative-ledger equations,
and model/observation certificates. No theorem in this item silently assumes
those are proved. The source program and schedule remain those of the plan;
there is no new parser/inference-to-initial-state result.

## Updated termination lemma ledger

| Plan lemma | Status for the new relation |
|---|---|
| L0 source/model invariants | **Proved.** `formed_old`, `formed_exact`, `stepModels`, `steps_models` |
| L1 formed-step decomposition | **Proved.** `GeneralNominalDownstreamOrder.formed_step_cases`; generated-site registration inherited |
| L2 administrative accessibility | **Proved.** `GeneralNominalDownstreamSteps.passive_accessible` |
| L3 fixed-capture Paterson descent | **Proved on integration**, unchanged; output-only binders excluded |
| L4 finite interval-sensitive cost readback | **Missing.** Existing projection containment/origin soundness retained |
| L5 source-derived, update-stable generation budget | **Missing.** New `grounded_iff_depth` and `snapshot_bound` prove only the fixed-snapshot prerequisite |
| L6 bounded future occurrence/source identities | **Missing.** Finite initial identities and deterministic fresh allocation alone do not prove it |
| L7 finite semantic packet/child signatures | **Missing.** Requires L6 and bounds on reports/materialized expressions; raw cached packets cannot be enumerated |
| L8 persistence/novelty | Existing fixed-packet commitment persistence inherited; finite-signature coverage still **missing** |
| L9 decreasing missing-fact count | Existing fixed-basis counting inherited; no basis derived for all future installations |
| L10 installation order implies Acc | **Proved conditionally** for the exact new guard in `GeneralNominalDownstreamOrder.accessible` |
| L11 reachable root child accessibility | **Missing** without Readback; `whereAccessible_of_readback` retains that explicit premise |
| L12 bounded complete rejustification | **Missing**, no new replay transition introduced |

The remaining L5 obligation is a source-derived bound on *future* useful
capture/observation refinements and emitted invocation paths, stable under
merge, discharge, and new independent explanations. The present support-depth
proof is not that bound. No new terminating scheduler, fairness premise,
source rank, finite-basis field, or declaration restriction is inserted.

## V5 bridge count: six of fourteen unconditional

[GeneralNominalDownstreamObligations.Remaining](../../lean/Yulang/GeneralNominalDownstreamObligations.lean)
has exactly eight fields. Its composition theorem fills the other six using
proved laws of this boundary, not caller-supplied replacements.

| V5 field | Status |
|---|---|
| progress | **Missing**; conditional on the explicit new InstallationOrder |
| execution | Proved for the new executor **conditional only on Progress** |
| halted | Proved for the new executor **conditional only on Progress** |
| closure | **Proved** |
| stepModels | **Proved** |
| frontierLocal | **Proved** |
| localIdentity | **Proved** |
| whereAccessible | **Missing**; conditional on general Readback |
| treeExecution | Proved for the new executor **conditional only on Progress**, with the target's own exactness/accessibility arguments |
| canonicalLocalOrder | **Missing** |
| dictionaryRefl | **Proved** |
| evidenceNode | **Missing** for this boundary; prior evidence modules are not silently transported across weakened stability |
| generatedChildren | **Missing** as a V5 field |
| initialReorders | **Proved** |

All SourceBoundary fields have concrete definitions in the new package;
being defined is distinct from satisfying these bridge obligations. Models,
RootPending, RootK2, CandidateK2, Survivor, Reorders, DictionaryEquivalent and
Evidence retain the previous nominal definitions through `state.current`.
InspectionPending adds downstream support deferral. Step/Stable use the new
relation; Generated retains complete journal generation. Checked and Initial
are unchanged. The noncomputable executor is parameterized by Progress;
no unconditional executor totality claim follows from its definition.

## Principal theorem statements

Names below are in the corresponding `Yulang.GeneralNominalDownstream…`
namespaces. Full binder types and all auxiliary statements are available in the
linked modules; every new public theorem is included in the new audit part.

```lean
-- Support
pool_exact (state : Tracked roles) (model : Assignment) :
  Slice state (dependencyPool state) model ↔ AllModels state model

trap_excluded (registry : Registry) (state : Tracked roles)
  (trap : Occurrence roles → Prop)
  (unresolved : ∀ producer, trap producer → ¬ Discharged state.current producer)
  (returns : ∀ producer, trap producer → ∃ child,
    Waiting state.current producer child ∧ ¬ Discharged state.current child ∧
    ∃ identity test, Need registry state child identity test ∧
      ∀ support, HeadSupported state support identity test →
        ∃ dependency ∈ support, trap dependency)
  (producer : Occurrence roles) (grounded : Grounded registry state producer) :
  ¬ trap producer

-- Steps
step_old (update : Step registry root before after) :
  GeneralNominalSupportSteps.Step registry root before after

formed_exact (formed : SourceFormed registry root state) :
  GeneralNominalSupportSteps.Exact state

stepModels (update : Step registry root before after) (model : Assignment)
  (valid : Models after.current model) : Models before.current model

closure (halted : ∀ after, ¬ Step registry root state after) :
  Stable registry state root ∧
    ∀ child, Generated state.current root child → Stable registry state child

passive_accessible (registry : Registry) (root : Occurrence roles) (state : Tracked roles) :
  Acc (fun next current => Passive registry root current next) state

-- Order: its essential premise is still present.
accessible (order : InstallationOrder registry root)
  (state : Tracked roles) (formed : SourceFormed registry root state) :
  Acc (fun next current => Step registry root current next) state

-- Concrete semantic journal, with a separate unproved transition bridge.
cut_journal_exact : GeneralNominalSupportSteps.Exact cutJournal
cut_journal_models : Models cutJournal.current journalModel
concrete_wrap_not_grounded : ¬ Grounded reg cutJournal kidW
concrete_downstream_head_blocked (support : List (Occurrence roles))
  (supported : Supported reg cutJournal support) :
  ¬ HeadSupported cutJournal support 2 (.nominal 0 1)

-- Any prefix or certified view satisfying these explicit facts is blocked.
first_P_and_W_blocked (certificate : PrefixCertificate state)
  (current : ∀ test observation, Head state.current.context.state 2 test observation →
    test = .nominal 0 1) :
  (¬ ∃ support, DecisionGuard reg state nextP support) ∧
  (¬ ∃ support, DecisionGuard reg state nextW support)
```

## Checks and workflow

| Command | Exit code | Result |
|---|---:|---|
| `cd lean && lake build Yulang.GeneralNominalDownstreamOrder Yulang.GeneralNominalDownstreamObligations Yulang.GeneralNominalDownstreamExamples Yulang.GeneralNominalDownstreamSiblingFixture` | 0 | Focused closure of all nine new modules; 699 jobs |
| `cd lean && lake build Yulang` | 0 | Aggregate build; 1803 jobs |
| `cd lean && lake env lean Audit/GeneralNominalDownstream.lean > /tmp/yulang-downstream-audit.log` | 0 | 109 public theorem entries |
| `git diff --check` | 0 | Whitespace check |

A separate Python check exited 0: all 109 audit entries use only propext,
Classical.choice, and Quot.sound; the new proof files contain none of the
prohibited proof constructs; the entire prior Yulang.lean byte prefix is
unchanged, followed by exactly nine import lines; frozen Audit.lean and
README.md match HEAD; all new local documentation links resolve. Development
builds initially exposed elaboration errors; the final commands above pass.
The full legacy audit and tools/verify-lean.sh were not rerun.

Files added: nine `GeneralNominalDownstream*.lean` modules, the new
`lean/Audit/GeneralNominalDownstream.lean` part, this design note and the small
[module guide](2026-11-13-general-nominal-downstream-module-guide.md). Files
changed: append-only imports in `lean/Yulang.lean`, an Item 4i pointer in the
main general-boundary note, and entries in `notes/design/INDEX.md`.
No old Lean definition, frozen Audit.lean/README, specification, plan inbox,
lake configuration, or git ref is changed.

The registered prover configuration and callable prover role are unavailable
in this worktree. The primary constructed the bounded guard/depth derivations;
a complementary regression agent constructed the explicitly scoped sibling
fixture. A separate read-only review checked the semantics and proof boundaries,
identified the discharge-path issue, and reviewed the depth argument. No
registered prover run or closure of B4 termination is claimed.
