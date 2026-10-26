# Goal-indexed checking admission — frozen producer handoff

Status: AUTHOR FROZEN; native checker and complete origin audit passed;
fresh independent nonauthor review pending. No acceptance or integration of
the new module is asserted by this producer receipt.

Primary baseline: `ff12ce5049cb7f26c7d873467c9a761ed49fc3e1`.
Start: 2026-10-26 14:08:15 UTC. Deadline: 15:08:15 UTC.
Budget: 3600 seconds, at most 28 focused checks, each at most 120 seconds,
one CPU/thread, Lean `-j1 -M1024`, monitored aggregate checker process-group
RSS at most 1280 MiB. Exactly 10 focused checks were used. No descendants,
Git, Rust, dependency, shared configuration or shared status writes.

## Frozen deliverables

- `notes/theory/lean/YulangClosure/OriginalCheckingAdmission.lean`:
  SHA256 `77a8dd74f5913814d3628f0aed189be24b4aafc4780839eaa57237676a157da7`.
  Frozen after clean module check9; check10 audited those exact same bytes.
- `notes/theory/2026-10-26-original-checking-admission.md`: paired complete
  source correspondence, proof scope, explicit residuals and discriminator.
- This handoff. Their final hashes are recorded together in the external
  artifact-manifest.json; the manifest does not rely on a self-hash in this file.

The earlier core-only checkpoint is separately frozen in
`tasks/agent-loop/inbox/20261026-checking-admission-interface-r4.md` and
`checking-admission-r4/core-freeze/`. Primary reports that checkpoint ACCEPTed
and published at `4c5fff3b2addbbea61a110865cb9273d10c9f97d` at 14:27:32 UTC.
No core bytes changed following its check3 census or publication:

| Core source | SHA256 |
| --- | --- |
| OriginalSourceGeneration | `0f25e53350edf9c452fd3c0f461602437ca2adf979859fda5e2492bcc403ae55` |
| OriginalSourceEnvironment | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` |
| OriginalSourceChecking | `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6` |

Generation was explicitly released early for PairK after check1. All core
files remained immutable afterward; no silent dependency refresh occurred.

## Original claim and changed premise

SG §3.2(4) requires D_currentGoalUpper for a finite Function observation child,
including composition intermediates. The old admitted relation had no goal
argument, and the accepted current-event Function theorem needed targetReadback
to align the binder descriptor with the target. The new path removes that
alignment premise by admitting at the current goal directly.

Kernel.checkingAdmitted has a backward-compatible legacy default and is used
only by Checking.function. Source forall/exists/execution/shared constructors
and Satisfies admission expressions, sourceRules/clientRules, Formula/compile,
raw invocation fields, Binder.arity and actual event keys remain unchanged.
Byte comparisons against the pinned baseline establish the unchanged source
builders/formulas/source-only admission sections. This is not a blanket
Judgment/Satisfies equivalence claim after correcting local Checking.

## Concrete construction and parent application

All names below are in `YulangClosure.OriginalCheckingAdmission`.

| Original obligation | Constructed declarations and exact boundary |
| --- | --- |
| Target-specific complete D | GoalDataAdmitted and GoalAdmitted use goal.upper, original CallOwner value/root, full CheckedDomain, original candidate-parent scope and deterministic decode. Non-invocation payloads delegate to unchanged DataAdmitted. |
| Both admission directions | goal_challenge_supplies_admission encodes every original goal challenge with its own view/event registration; goal_admission_recovers_challenge recovers its exact raw data, subject and full target-domain proof. |
| Real observation occurrence | goal_invocation_has_active constructs the actual decoded child and active CallInput. No inactive identity is called observation safety. |
| Default and legacy compatibility | default_checking_admission, admission_update_keeps_checking, aligned/initial recovery, and all seven existing wrapper conservation roots. No general goal-to-legacy conversion. |
| Correct wrapper order | goalFunctionKernel applies the goal override AFTER legacy functionKernel; registered_kernel_admissions proves both final admission fields and the exact FunctionShape leaf predicate. |
| Unchanged whole runtime tuple | encode_retarget, decode_encode_input, encoded_scope_retarget, encoded_event_path_retarget; descriptor retargeting never alters runtime or event identity. |
| Genuine source incidence | source_app_admission_recovery gets the exact unannotated App premise from sourceRules; goal_app_callable and goal_lambda_callable use Root.withSource/sourceCallOwners. App reads callee.returnedValue, not its eventual result. |
| Native receipt supply | native_received_supplies_goal_admission composes the actual Received/owned Receipt encoding and native insertion theorem with goal admission. True view/event registration equations remain explicit. |
| Observation semantic action | goal_observation_child_transport consumes the recursive child meaning at every goal-admitted candidate. It uses authentic observation.upper=goal.upper incidence and the raw-input round trip, with no binder/target descriptor equality. |
| Actual finite Function node | goal_function_checking_constructor retains both Checking children and returns the current-event FunctionAt from explicit local semantic IHs. |
| Discharged semantic IHs | goal_function_children_at_meaning obtains both child meanings through the actual mutual checking_sound induction; target guards/captures come from finite registered Proof code. |
| Completed source application | checked_current_function_from_meaning unfolds completed source Meaning and applies the checked children to obtain the target current-event Function core. It does not conclude future target membership. |

The viewReadback/eventReadback hypotheses in every new Function theorem range
over Challenge(state.goalRow binder goal) and that target's own checkedIncidences.
Retarget preserves the complete raw input; it does not imply arbitrary checked
incidence invariance. No law quantified only over the binder row is reused for
an intermediate target.

The old accepted conditional Environment and Checking roots remain valid.
The corrected generic finite Checking induction covers every original finite
constructor; its interpretation remains the registered-proof Kernel, not an
asserted complete original native registry instance.

## Bidirectional nonconstant discriminator

The explicit finite fixture has Descriptor=Interface=Carrier=Bool and
carrierAccepted(interface,carrier) iff interface=false or carrier=false.
Hence D(false)={false,true} and D(true)={false}; both are nonempty.
Its source-owned CallOwner table is generated from an actual raw App/Lambda.

- broad_source_narrow_goal proves carrier=true is legacy-admitted at binder
  false and rejected by target true.
- narrow_source_broad_goal proves the reverse missing-challenge case: carrier=true
  is admitted at intermediate target false and absent from binder true's domain.
- both_domains_nonempty supplies carrier=false to every combination.
- source_and_target_descriptors_differ proves the targetReadback equation is
  unavailable in both separating cases.
- same_encoded_invocation and same_actual_event_key prove unchanged raw identity.

goal_domain and legacy_domain prove exact admission characterizations, not
only one convenient positive example. This fixture tests admission plumbing;
it is not claimed to instantiate all original Yulang primitive semantics.

## Complete verification and retained failures

Exact native toolchain: Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake
`5.0.0-src+eb6cafb`. No toolchain installation or dependency/configuration change.
The native executable and isolated project are recorded in every command log.
The runner pins one CPU, LEAN_NUM_THREADS=1, Lean -j1 -M1024, a 120-second
process-group deadline, and the monitored 1280 MiB aggregate RSS ceiling.

| Check | Result and actual scope |
| --- | --- |
| 1 | PASS: minimal Generation seam; immutable release for PairK. |
| 2 | PASS: full changed core dependency cone and OriginalEffectHygiene consumer. |
| 3 | PASS: complete core-origin census, 2399 declarations, 943 theorem constants, all 152 previous authored roots. |
| 4 | FAIL retained: aligned legacy invocation branch needed explicit rw of the descriptor equation after unfolding. |
| 5 | PASS: concrete admission/recovery, transport/constructor, registered current-event application and conservation. |
| 6 | FAIL retained: fixture decide could not synthesize Decidable through opaque semantic sort projections; explicit field readback lemmas replaced that attempt. |
| 7 | FAIL retained: fixture baseRoot record indentation error, with resulting dependent elaboration errors. Fixed only the new fixture. |
| 8 | FAIL retained: the Boolean characterization proofs retained reflexive raw-value/root equalities and id applications; direct pair projection/construction finished them. |
| 9 | PASS: final complete new module, including native supply, completed Meaning application and both domain directions; no warnings. |
| 10 | PASS: complete new-origin type/axiom census; no warnings. |

Every call retains its actual source/configuration snapshot from check1, exact
command, elapsed time, source manifest, exit, peak sampled process-group RSS
and full log. No timeout or memory-limit termination occurred. The maximum
sampled group RSS was 1,197,707,264 bytes in core census3, below 1280 MiB.

New-module census: **90 originating declarations, 65 theorem constants, all
45 authored theorem roots**, including private and generated declarations.
Every origin has its complete type and #print axioms output. No project axiom
or unexpected axiom was found. Actual axiom union:
`propext`, `Quot.sound`, `Classical.choice`. Overlapping per-origin counts are
67, 38, and 26 respectively; exact names and printed universe suffixes are
retained in axioms.json. The fixture's source-registry definitions and related
source incidence roots contribute Classical.choice dependencies; no claim of
axiom-free results is made.

The lexical source scan found no code sorry/admit/project axiom/unsafe/
native_decide/skipKernelTC. An initial postprocessing scan matched the English
word "admit" in a block comment; that false positive and the corrected lexical
comment-stripping scan are retained. It did not change code or rerun Lean.

## Evidence locations

Owned scratch: `/workspace/scratch/f98087c7ac1a/checking-admission-r4/`.

- input-manifest.json: exact 15 initial code/configuration inputs, baseline,
  start/deadline and bounds before execution.
- snapshots/01-generation through snapshots/10-census: actual checker inputs.
- checks.json and all numbered logs: complete success/failure history.
- core-freeze.json and core-freeze/: separate immutable published core evidence.
- code-freeze.json: final new-module SHA and exact successful snapshot.
- project/GoalAdmissionAudit.lean, required-roots.json, 10-census.log:
  complete originating census and every full type/axiom report.
- axioms.json and validation-summary.json: per-origin printed/normalized
  dependencies and validation reconciliation.
- artifact-manifest.json: final new module, note, handoff and evidence hashes.

The new census log is 185,627 bytes, SHA256
`33ad8941e334b0a64b25d46b94a98b6fff74d85ca3b8085a38daa7d069abf298`.
No core census was repeated after its immutable checkpoint. Shared default
integration and current-root imports remain primary-owned.

## Precise remaining original parent seam

No KernelSound/LocalLaws/full GoalMeaning oracle, new provider acceptance filter,
arbitrary observation inclusion, or silently narrowed source domain was added.
The original current-goal admission mismatch is repaired and exercised by the
actual finite checking induction and source/native incidence suppliers.

The next owner is actual future-event hereditary Function registration:
OriginalSourceChecking.FunctionShape.proof must cover every value event probe,
while stateClause's domain branch currently guards the input by equality with
the decoded current event. A constructive next packet must register/read back
the domain and observation child at that same original later event, with the
retained fixed frame prefix, actual view/receipt, guard and capture incidences.
The current-event result and descriptor retarget invariance do not supply that
registration automatically; it must not be replaced by an assumed future
GoalMeaning law.

Complete original primitive/structural/native registry correspondence, genuine
recursive L4, and native success-to-satisfaction remain separate obligations.
Neither refuted provisional-candidate checking-closure argument is used.

## Stop and review state

All producer source/note/handoff writes are STOPPED at final manifest freeze.
No checker processes or descendants remain running. Core files and new module
are immutable review inputs. Primary owns the fresh independent nonauthor
review, final shared integration, status, commit and push. This packet does not
self-certify independent acceptance.
