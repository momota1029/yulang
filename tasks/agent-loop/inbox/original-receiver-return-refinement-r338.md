# R338 native receiver Return refinement — frozen handoff

Assignment `R338-RETURN`, handoff revision 1. Parent assignment
baseline `8e7d98d7e`; worker `/root/r338_return`; no children or Git mutations.
Exact repository leases: this file and
`notes/theory/lean/YulangClosure/OriginalReceiverReturnRefinementR338.lean`.
Scratch/cache lease: `/tmp/yulang-r338-return` only. Model/effort observed by
worker: UNKNOWN. Budget 3000 seconds; aggregate checker coordinated with Luna.

## Original obligation and source correspondence

Original parent: original source Union/whole Call EI and unchanged R159, as
fixed by `tasks/agent-loop/sprints/actual-source-union-r338.md`. Local consumer:
`OriginalSourceInterpretation.function_return_result`, retaining arbitrary
original Inputs, function membership, SAME actual semantic provider, original
independently admitted challenge, execute, checking readout and trace form.
The actual whole-language parent remains OPEN.

Governing original state/Return is `docs/yulang-whole-language-semantics-ja.tex`,
“状態と結果” and “引数を受け取ってから実行する” (lines 220–263).
`docs/yulang-operational-type-safety-ja.tex` opening correction explicitly
forbids unexamined transfer of its old resume semantics. Relevant corrected
completion is `notes/theory/2026-10-24-corrected-machine-simulation.md` §5:
owned completion removes exactly its execution owner without rewriting old
immutable source evidence. These research manuscripts are not blanket semantic
approval. Authoritative EI is
`notes/design/2026-10-24-computed-call-result-constructor.md` §§3.3–5: only an
actual receiver Return populates the original result/provider/current-world
slot; all independent developments, providers, arms, admission and future
clauses remain required.

Actual code read: `tools/inference-playground/src/runtime/machine.rs`,
`return_value` / `Frame::ReceiverReturn`, `leave_owner`, and `owner_active`.
The local boundary follows `step` taking state into a local variable, then token takes and frame pop in `return_value`. On error, `step` replaces its temporary Stopped(Running) sentinel with Stopped(Unavailable(error)); the raw input carried by the Lean invalid result is evidence, not a claim that State::Return persists.
ReceiverReturn copies input value/view/dispatch, normalizes Value interface,
then calls leave_owner(Invocation(activation), true, previous), then assigns
State::Return. Native leave checks current owner, pops active_receivers, checks
top, gets invocation, checks active, retires it, restores previous owner.
Wrong top/missing/inactive invocation can fail AFTER pop. Failure is not an
atomic world identity. Existing `SourceIdentityWorld.Control.leave` records
successful outcome/rejection only; R338 separately retains failed post-control.

## Construction and current evidence

Module namespace:
`YulangClosure.OriginalReceiverReturnRefinementR338`.
- `leaveOwned` sequentially models the exact owned=true branch, including every
  invalid-source-reference exit and failed pop side effects.
- `NativeControl` retains full call/provider/active descriptors and native
  outer-to-inner vector order. `nativeLeaveOwned` uses finite List vectors;
  `native_leave_refines` proves full successful/failed control projection.
- `receiverReturn` computes normalized output from INPUT packet and sets the
  represented Return only after successful exit.
- `receiver_return_construct` derives actual Return/returnOwned, restored owner,
  exact stack, target retirement, unchanged other invocations and table size,
  all represented environment/cell/receiving/rest stores, and exact output
  value/view/dispatch/interface from independent raw input guards.
- `receiver_return_failure` proves failed packet/store/owner/table preservation
  while retaining the possible already-performed pop.
- `receiver_return_from_vectors` applies the construction to raw finite snapshots.
- `exitEvent` computes the new current.world in existing NS Configuration.
  `nativeResult` uses the SAME existing eta.views.value/root interpretation of
  the actual native input; eta, shared witness, provider registry, aliases and
  residual configuration remain the original fields. These are data readouts,
  not event-coherence, compatibility, world validity or provider certificates.
- `exit_event_differs` and `function_rejects_pre_exit` apply the R337 original
  Event/function consumer with DERIVED native transition, replacing R337's
  successful-return equation premise with raw pre-exit guards.
- `post_exit_return_iff` applies the unchanged original pure-Return clause at
  the actual constructed post-exit Event and discharges its event equality.

Check 1: pinned direct module check exit 1 (0.85 s), with local shape/layout,
Option simplification and let-unfolding diagnostics; full log retained.
Check 2: exit 1 (0.69 s), only absent Store.ext helper; replaced with direct
Store constructor equality/function extensionality.
Check 3: exit 0 (0.94 s), clean, all then-current 13 theorem roots.
Check 4: selective Lake build, exit 1: all 18 dependency modules and final core
module built, but Lake's configured -M1024 exhausted memory in both raw-artifact
modules after import Lean. The full failure/panic diagnostics are retained in
`build-4.log`. No configuration or source was weakened. Sequential direct
-j1 -M2048 artifact compilation then passed for the exact authentic R338 copy
(`native-build-5.log`, exit 0) and the namespace-wrapped authentic R335 artifact
(`legacy-build-6.log`, exit 0). Actual selected application compilation passed
(`selected-build-7.log` and `selected-build-8.log`, both exit 0).

Bundled skill checker: `helper-9.log`, exit 0, all **14 core theorem roots PASS**.
Its exact argv is `checker-command.json`; the project and Lake paths below
were supplied, with timeout 300 seconds and TMPDIR inside this lease. The
helper's configured -M1024 audit succeeds for the core module. The larger raw
artifact modules instead use the explicit -M2048 manual audit.

Final exact core source refresh: `final-core-11.log`, exit 0 (0.79 s), command
`lake env lean -j1 -M2048 YulangClosure/OriginalReceiverReturnRefinementR338.lean -o .lake/build/lib/lean/YulangClosure/OriginalReceiverReturnRefinementR338.olean`.
Final complete type/kind/axiom audit: `final-audit-12.log`, exit 0, command
`lake env lean -j1 -M2048 R338Audit.lean`. All **25 authored roots** (14 core,
11 concrete selected applications) have complete #check @name and #print axioms
output; the helper's validator accepted the entire ordered audit and theorem
kind/axiom whitelist checks. Only **propext** and **Quot.sound** occur.
No Classical.choice, project axioms, sorryAx, native-evaluation assumptions or
checker bypasses occur. `axiom-results.json` contains EVERY exact list.
Source search across the changed dependency cone found only three prose matches
for axiom/admit in existing comments; `source-audit.txt` preserves them.
Default/root integration build and independent review are not claimed.

Installed native Lake resolved read-only with `elan which lake`:
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Actual versions: Lake 5.0.0-src+eb6cafb (Lean 4.35.0); Lean 4.35.0,
x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc.
Commands used in isolated project:
`lake env lean -j1 -M2048 YulangClosure/OriginalReceiverReturnRefinementR338.lean`.
The exact frozen R337 dependency source hashes match current repository;
18 transitive module hashes are in scratch `dependency-hashes.json`.
No shared .lake outputs are written. CPU/RSS were not instrumented.

## Authentic native evidence and limits

Read authentic R335 r2 artifact
`/tmp/yulang-r335-native/r335-operation-source-r2.lean`, SHA-256
`6783f166e8da158d2bb8047300999bc6eb60284a8027d3bf236905291306b5e7`.
It retains selected activation 8, previous owner Invocation(6), call occurrence
12, source provider make occurrence 7, actual returned packet value/view 4/5,
Value/no dispatch, step 63; selected-definition completion has the same packet
at step 73 under ModuleRun. Its Return observation is BEFORE leave_owner and
does NOT itself authenticate raw stack, invocation activity or post-exit world.
R338 authentic witness `/tmp/yulang-r338-native/r338-operation-source.lean`,
SHA-256 `70c080855a0f57700b0521e7c0c92ff0794d0ef3db5bbd0a7ecc609e780586ed`,
was copied BYTE-FOR-BYTE to isolated `YulangClosure/R338NativeArtifact.lean`.
The scratch `YulangClosure/R335LegacyArtifact.lean` wraps the authentic R335 r2
bytes in namespace Legacy (only import/namespace wrapper added; its original
source hash above remains the provenance). No runtime receipt was fabricated.

The actual snapshot has current Invocation(8), native active vector
[0,4,5,6,8], and nine full invocation descriptors before exit. The computed
outcome equals the recorded post snapshot: current Invocation(6), vector
[0,4,5,6], all nine rows retained with ONLY row 8 inactive, complete call/provider
source metadata unchanged. Incoming and normalized outgoing tuples are value/view
4/5, Value, no dispatch; both native snapshot steps are 63. Exact source call
and source provider match the same-run R335 retained rows; the selected-definition
completion retains the identical packet at step 73. The historical R335 theorem
compares handles/occurrences/step data, not run identity across separate runs.

Concrete applications in scratch namespace `YulangClosure.R338Selected`:
`table_indices`, `native_exit`, `input_guards`, `packet_from_input`,
`selected_trace_join`, `authentic_r335_legacy_join`, `world_return`,
`computed_world_is_observed`, `computed_event_is_observed`, `event_changes`,
`original_trace_iff`. The entire native outcome is DERIVED from before-inputs
and equated with observed after-data; successful output is never a hypothesis.
`computed_world_is_observed` retains arbitrary environment/cell/receiving/rest
stores: these stores were not captured by the finite snapshot. Their preservation
comes from the source-branch model, not from a claimed runtime comparison.
`original_trace_iff` applies the original Return consumer at the observed post-exit
control with exact raw value interpreted by the SAME original eta.views.value/root.
The raw value handle is not substituted for an original semantic value.

Represented: complete local owned receiver exit, arbitrary payload/view data,
full finite control vectors, all failure branches and all represented World
stores, original NS Event fields and shared eta/witness.
Unrepresented: other frame branches, borrowed owned=false leave branch,
return_value's earlier token/frame operations, test journal mutations and outer
error driver, whole source execution/Inputs, world coherence and validity,
whole-tuple lawful action, semantic provider/future law, independent whole-Call
arms, license/admission/checking and universal EI. A source provider SourceSite
is never equated with `b.Provider`; finite trace evidence is not universal EI.

First remaining parent premise/owner: original Inputs/traceForm/execute and
post-exit world/value/observation membership from the actual whole source
operation, owned by original semantic/source proof lane (Luna). Raw finite
snapshots can discharge operational guards only; they do not prove these
independent semantic premises. Fresh independent review and primary integration
are pending. The source/semantic parent, universal EI and production gates remain
OPEN. This is kernel-accepted local operational mathematics plus authentic finite
source/native data application, not self-certified source correspondence.

## Frozen bytes, complete axiom census and cessation

Core artifact SHA-256:
`27048334114fafb2e63d81ecddf64d3a2c6d74c4843b3238670beade03afae19`.
Concrete scratch `project/YulangClosure/R338Selected.lean` SHA-256:
`c3f39289dc185c6dde3bc1f0a9aee94385e0548fe5c09019d7ed2810f0f42885`.
Complete final audit SHA-256:
`d45f7c442c2f2a1115a6088bd9d0a9a72c2e096a683b52ca4a0e4a7371468d66`.
Dependency manifest SHA-256:
`a62603eb7fb9c37ee84eee6f54db940782d182f9f668c52d66f028e8908f7035`.
Contract SHA-256:
`b416b1731da2bd1bd9e83d34fcee300237ca06b21a48634ebfec139092458215`.
R337 import SHA-256:
`b6d524a13d74184d7b76e77c03be08ad3ed2183f21b958ee0c6d453a4e0be462`.
SourceIdentityWorld SHA-256:
`6019fd9d57cde50183e016bd0c72de2c6eee72009065d85119fb0348dbcf0168`.
Native source after concurrent producer edits (read-only input) SHA-256:
`1832020d095134dd69637bb1eb8f9eea70499037124c0654417190d6dba78803`.
The originally read native baseline hash was
`3727e1f4f32b9bed251a30224bd63b87a575d9ef84b97564f95e5774800a11c5`.
Source authority hashes read:
EI `2f3a5461b6dacaa29e881ba8b3003120b912e441dd5e4c47fc4ccaa27d3b31a6`;
original semantics `6246e7dc179a795b372603eac8cd64bf783ba69e9a4a733bcfc012ebd6869612`;
operational manuscript `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`;
corrected simulation `fffb4f1540739020a0702d4f7b07d41cd9b68a9063f36d24292914b84e6b606d`.

Core namespace prefix below is
`YulangClosure.OriginalReceiverReturnRefinementR338`:
- []: leave_owned_failure, receiver_return_failure, native_result_fields.
- [propext, Quot.sound]: vector_retirement, native_leave_refines,
  receiver_return_from_vectors.
- [propext]: leave_owned_refines, leave_owned_construct, wrong_top_pops,
  receiver_return_refines, receiver_return_construct, exit_event_differs,
  post_exit_return_iff, function_rejects_pre_exit.
Selected namespace prefix is `YulangClosure.R338Selected`:
- []: table_indices, packet_from_input, selected_trace_join,
  authentic_r335_legacy_join.
- [propext]: native_exit, input_guards.
- [propext, Quot.sound]: world_return, computed_world_is_observed,
  computed_event_is_observed, event_changes, original_trace_iff.

All scratch, audit inputs, exact commands, failure/success logs and copied build
outputs are under `/tmp/yulang-r338-return`; only this leaf wrote that tree.
`artifact-hashes.json`, `dependency-hashes.json`, `theorems.json`,
`axiom-results.json`, `checker-command.json`, `source-audit.txt` are the indexes.
No compiler, tests, root imports, shared records, manifests, global configuration
or Git state were edited. No descendants. No background processes remain.
First scratch creation 2026-11-03 13:50:30 UTC; final audit completed before
14:10 UTC (under 1200 seconds for the instrumentable scratch interval; earlier
read-only setup not timed). Bound 3000 seconds was not exhausted. CPU/RSS and
exact runtime launch timestamp are UNKNOWN; no unobserved budget is reclaimed.
Core and scratch writes stopped at the final frozen check. Handoff writes STOPPED
upon this revision's submission. Primary owns review, integration, any root
import, scratch retention/cleanup and all still-open semantic premises.
