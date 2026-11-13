# Actual boundary agreement with explicit provenance policies

Date: 2026-11-14. Status: **Draft; checked operational agreement and conditional
transfers, not a complete semantic B4 instance.**

This continues the [owner-decision audit](2026-11-14-actual-boundary-agreement.md)
under the user's explicit instruction to parameterize the unanswered choice.
The authority and verbatim owner quotations remain in that note's §2 and
[spec §6](../../spec/06-roles.md), with [B4 addenda 1–7](2026-11-08-b4-main-statement-draft.md).
Neither owner option is selected here. Existing definitions and Step are frozen.

## 1. Parameters and exact local meaning

`GeneralNominalActualAgreedLocal` defines the following independent predicates.

| Predicate | Exact scope |
| --- | --- |
| `Installable` | `FeedbackSteps.Installable` and some support satisfying the entire actual `PacketGuard`. Novelty is excluded: an already committed packet needs no installation action. |
| `Available` | A packet with the exact occurrence, declaration ID and children, either Installable or recorded in this registry's journal and Committed. |
| `InspectedCycle` | A registered site for the occurrence, a checked visible head-ready alternative with located bounds, and a tested actual origin whose represented source is `RecursAt`. It uses the recovered actual inspection report. |
| `ProvenanceGap` | A **base-installable** packet for the occurrence lacks `GenerationGuard` or `InputCoherence`. It does not quantify over malformed candidate packets, or call every installation failure provenance. |
| `Blocked` | The old survivor predicate has a unique key/children pair, but no matching Available packet. |
| `ResidualGap gap` | `Blocked` holds and the supplied gap predicate does not. These remaining operational obstacles are explicit, not proved to be owner-approved semantic deferrals. |

The parameter `gap : Registry → Tracked → Occurrence → Prop` is arbitrary.
The concrete boundaries instantiate it with `ProvenanceGap`:

- `pendingBoundary` uses `defer = true`.
- `completeBoundary` uses `defer = false`. Its selection-to-availability and
  generated-children results require absence of the gap. `GapFree` states that
  absence for all demands at checked reachable snapshots; it is an explicit
  obligation, not a component hidden in Initial or Checked.

Survivors, declaration identity and children are unchanged. RootPending and
RootK2 are retained. CandidateK2 is **legacy CandidateK2 or InspectedCycle**.
InspectionPending is the disjunction of:

1. the old feedback inspection-pending predicate;
2. absence of the shared settled `DecisionGuard`, independently of candidate count;
3. `ResidualGap gap`;
4. `defer = true ∧ Blocked ∧ gap`.

The generic V3 Local rules enforce the priority: unknown unnamed heads first;
then either K2 rejection; then inspection pending; then zero survivors,
ambiguity, or unique selection. Thus an unsettled-output-only justification
remains pending even with zero or multiple survivors, while an actual cycle
is rejected before this deferral once the unnamed heads are known.

This is deliberately an **operational agreement boundary**. ResidualGap can
include unresolved merge/choice/joint-consistency obligations, missing actual
location certificates, or an incomplete source producer. Neither this residual
predicate nor every old inspection-pending case has been identified with exactly
the owner's semantic deferrals. Their specification completeness remains open.
The user-authorized provenance parameter does not decide those other questions.

## 2. Agreement results and limits

`local_functional` holds for every parameter and state; `local_total` requires
only a checked registry, as the existing V3 interface requires.

`selected_iff`, assuming `defer = true ∨ ¬ gap registry state root`, states:

```text
new Local selected(key, children)
  ↔ old feedback Local selected(key, children)
    ∧ no actual inspected cycle at the registered sites
    ∧ shared DecisionGuard
    ∧ Available(key, children).
```

In particular, selection implies installable-or-recorded-and-committed.
The installed direction still requires current old selection, shared head
justification, and absence of actual K2; a stale historical packet cannot
override a current rejection. `policies_agree` proves the Local relations
coincide when the gap is absent; the boundary version uses reachable `GapFree`.

`installable_selected` proves the reverse direction under absence of the
global actual-cycle predicate. The actual guard directly proves that every
alternative at **the installing site** is acyclic (`installable_site_acyclic`).
It does not quantify over other sites with the same occurrence. Therefore
`installable_selected_unique_site` exposes site uniqueness, and
`initial_installable_selected` discharges it at every initial state from the
singleton site list. The actual Display installation supplies a nonvacuous
`display_selected` theorem for both policies.

For arbitrary reachable snapshots, transport of actual inspections between
sites with the same occurrence is still missing. Interval fit alone does not
identify their actual origins. This is not repaired by alias reflexivity or
merge closure.

`inspected_cycle_rejected`, `root_cycle_rejected`, and
`candidate_cycle_at_site_blocks` connect cycle witnesses to diagnostics and
actual guards. `rejected_exact` exposes all rejection alternatives, including
the retained legacy K2 predicates. It does **not** assert that legacy
endpoint-based rejection is equivalent to actual-position rejection. The
frozen installation relation still contains those older predicates.

## 3. V5 fields

`GeneralNominalActualAgreedBoundary.boundary` keeps actual Step and InitialSource.
`reachable_iff_sourceFormed` establishes exactly the actual reachability scope.

| Field | New result |
| --- | --- |
| closure | Unconditional structural transfer for both policies. |
| stepModels | Unconditional, through actual-to-shared Step and model inclusion. |
| frontierLocal | Chosen frontier agrees with the new Local, using its totality/functionality. |
| localIdentity | Definitional identity with the new V3 Local. |
| dictionaryRefl | Existing dictionary equivalence reflexivity. |
| initialReorders | Existing source-formation reorder theorem; Initial is unchanged. |
| generatedChildren | Unconditional for the pending policy; under `GapFree` for the complete policy. A stable selected node is committed, hence its exact child edges are present. |
| execution / halted | `executor_exists` constructs these field shapes from supplied reachable accessibility, by the existing `terminal_of_accessible`. Diagnostics are a separate function argument. No tree correctness is inferred. |
| whereAccessible | Transfers from the existing `CycleReadback.Readback` producer. Producing that premise generally remains open. |
| progress | Not worked on; no new execution-termination result. |
| treeExecution / canonicalLocalOrder / evidenceNode | Open for these boundaries. |

No `B4Bridges` record or complete B4 statement is asserted. Merely supplying
arbitrary diagnostics to `terminalExecutor` does not fill `treeExecution`.

## 4. Provenance completeness and the additive repair

Unconditional results cover leaf implementations: `leaf_certificates` proves
GenerationGuard and InputCoherence for any packet without where-children.
`leaf_registry_no_gap` proves absence of the concrete provenance gap for any
registry consisting of such declarations, at every state. General completeness
from source-known/justified heads, including general point-root reachability,
is not established.

The source audit located two precise implementation mismatches:

1. `ActualInspectionSteps.inspection` reads `recover state packet.site`, whereas
   `SharedCaptures.inheritedReport` reads raw `packet.site.inputs`.
   Shared installation stores raw child sites. Existing
   `CompoundEmission.historical_child_root_recovered` proves recovery of a
   missing compound nominal child root along an actual trace, conditional on
   the compound shape and endpoint facts. That recovery is not written back
   into the site's input list used by GenerationGuard.
2. `Captured`/`InputBound` demand consequences of `packet.Holds` alone.
   `Packet.Holds` ignores `site.inputs`. A recovered endpoint equality may
   instead need the current journal's Models. Changing the report alone
   therefore cannot establish the full private-model certificate.

`GeneralNominalRecoveredProvenance` supplies bounded additive repair pieces:

- A recovered packet has definitionally identical Holds and children, and
  its inherited report equals the actual inspection report (`report_agrees`).
- `register` appends the recovered version of a registered site.
  `register_models` proves exact preservation of the journal model set.
- Journal-relative `Usable` and `Generation` state the needed model scope
  explicitly. Old private certificates imply these; the converse is not assumed.
- A state-indexed `Emission` permits soundness from both old journal Models
  and packet.Holds. `install_models` proves the same exact model equation as
  before: new Models iff old Models and packet.Holds.
- `recoveredEmission` recovers child sites against the **provisional post-packet
  journal**, so fresh child endpoint equations from this packet can be used.
  `recovered_emission_fills` proves that a missing input is retained as the
  lower source origin whenever the provisional journal equates its endpoints.
  `preexistingEmission` is the weaker variant using only the earlier journal.

No interval interior is selected. No full-journal fact is promoted into trusted
head justification. These new operations are not transitions of the frozen
actual Step: incorporating them requires a separately specified repaired
relation and its invariant proofs. Constructing all journal-relative capture,
repeated-origin agreement, and materialization certificates is still open.

The closest existing explicit compound installation fixture is a Shared Step,
not an actual-inspection Step with complete Safe/AlternativesSafe certificates.
It is not used as a concrete reachable point-root counterexample. The gap
identified above is an exact conditional data-flow mismatch, not a claim that
a particular checked point-root program has been proved permanently blocked.

## 5. Review and checks

A separate read-only reviewer checked the new definitions and proof statements.
The review found and prompted fixes for cardinality-dependent output deferral,
overbroad provenance witnesses, and recovery before fresh packet equations.
Fresh review found no remaining blocker in the inspected scope. No registered
prover role was available; the primary constructed the proofs directly.

Final checks from the repository root:

| Command | Exit code |
| --- | --- |
| `cd lean && lake build Yulang.GeneralNominalActualAgreedLocal Yulang.GeneralNominalActualAgreedBoundary Yulang.GeneralNominalRecoveredProvenance Yulang.GeneralNominalActualAgreementExamples > /tmp/yulang-agreement-focused.log 2>&1` | 0 |
| `cd lean && lake build Yulang > /tmp/yulang-agreement-build.log 2>&1` | 0 |
| `cd lean && lake env lean Audit/ActualBoundaryAgreement.lean > /tmp/yulang-agreement-audit.log 2>&1` | 0 |
| `git diff --check` | 0 |
| `python3 /tmp/yulang-agreement-scope.py` | 0 |

The aggregate build completed with 2301 jobs. The standalone audit covers all
78 public declarations in the four new modules and reports only `propext`,
`Classical.choice`, and `Quot.sound`. Initial focused builds returned 1 while
elaboration and proof errors were repaired; the final checks above all pass.
The scope check verifies append-only edits, module imports, audit coverage,
allowed dependency names, local document links, and the absence of forbidden
proof escapes in the new modules. It does not prove any open source invariant.

Only four new
Yulang modules, a standalone audit, this note, and permitted import/INDEX
appendices are part of this continuation. The earlier owner-question note is
left unchanged. No git ref, frozen configuration, or existing proof is changed.
