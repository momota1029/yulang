# R26 Lean handoff — checked conditional projection; source application OPEN

Author/runtime identity: `/root/r24_lean`, resumed session `R26` / assignment `ANNOTATION-HYGIENE-NATIVE-EVIDENCE/20261030-R26`. Observed model/effort: UNKNOWN. Actual active start: `2026-10-29T19:40:39Z`; fixed 600-second end: `2026-10-29T19:50:39Z`.

Status: the pinned checker **passed all 22 requested theorem declarations**, including exact printed types and complete transitive axiom lists, in audit 2. The result is a checked abstract conditional projection. Independent review, authenticated native/source application, the original parent and production remain OPEN. Both heavy processes have stopped; no further audit is authorized or planned.

## Fixed authority and input pins

- R26 contract `tasks/agent-loop/sprints/effect-permission-native-evidence-20261030-r26.md`: `8b2fcc72995472465b23fc397f257d07a035b0b1ba15f8f62ee31ae705dc11e5`.
- R26 manifest `tasks/agent-loop/sprints/effect-permission-native-evidence-20261030-r26-inputs.json`: `ec31c06563e6835101647272ce46930be55230481862621d8757b1193387e97d`.
- Source baseline `9a74a70a32ebda716a00c7203d8e606343cf442a`; schema R1 digest `686c96c8f8b5417b075a18954f773ad4071996e51e809d65040a87441c342c3c`.
- Frozen R24 candidate: `isolated/ep-hygiene-r24/project/notes/theory/lean/YulangClosure/CallbackHygieneCorrespondence.lean`, SHA `4bb9eafe2c0f7123c4d43722083190b9f7c78c2e0f6661160c5ccc56da1f7083`.
- Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5, SHA `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`.
- Governing effect policy/corrections: `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1.1,1.2,3,4, SHA `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`.
- Birth-level SCC correction: `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6, SHA `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`.
- Source map/execution references verified at manifest hashes `cb3f1009e80f0f9f7a1bf2575b4144e002a72f21e474c66b441e1f626a1e4d4a` / `a1d8c47550e8925220623e0401410556d92719aff5590c459ac4c2e88306800b`.
- Pinned R26 toolchain/project/dependency manifest and README matched all four R26 manifest pins. No external package or global default was changed.

The parent retains every supported original source program/history, original source scopes, complete Call/effects, correlated evidence and one joint admissible strategy. No bounded projection result closes the parent, required principality, soundness, progress, termination or production gate. The fixed-birth induced graph correction changes qualification only. Annotation permission never supplies actual effect inflow; the actual Catch handles a contribution; unknown variables and their dependencies remain in the parent scope.

## Exact repair and artifact

Changed only `isolated/ep-hygiene-r26/project/notes/theory/lean/YulangClosure/CallbackHygieneCorrespondence.lean`: SHA `0621f43739c12ce1e7919a50de129414a4748d8359bf46740babd69f4854011e`.

Copied the authenticated R24 candidate and removed nine redundant leading State binders from the constructor alternatives inside `YulangClosure.CallbackHygieneCorrespondence.step_conserved` and `.step_events_before`. The existing Step index already fixes that State. Every definition and all 22 theorem statements are preserved exactly. `lean-scratch/repair-receipt.json` proves textual identity outside these two proof bodies and records all nine replacements; this preservation receipt is a source check, not independent proof review. R24/R25 bytes were not edited.

The frozen candidate's source-owner map remains: receiving.rs callback annotation/entry/Name-Apply/use; machine.rs result-consumer/request event mint; exact Catch operation/payload/event/arm commitment; separate ordinary-return, request-unwind and shallow-discard branches. `abandon_suffix` clears pending global materialization cells, not actual `write` effect requests. The relation branches rather than requiring T1–T14 linearly. Permission, actual request, selected consumer, immutable evidence and lifetime coordinates stay separate.

## Actual audit 1

Read-only installed lookup `elan which lake`, run from the R26 Lean project, exited 0 and resolved `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.

The frozen checker script SHA is `a4f10b70297cbf4d8b5bc0c7526bc29783eaf417f1f70e53eeea341d1150dde6`; an unchanged copy is under R26 `lean-scratch/check_lean.py`. It was used directly, with no manual audit bypass. Exact full argv, including all 22 repeated `--theorem` flags, is in `lean-scratch/audit-command.json` and `.txt`; the actual checker argv is also in `audit1.resources.json`. Project and native Lake were explicit. The audit wrapper pinned itself and descendants to CPU 0, set task-local TMPDIR and LEAN_NUM_THREADS=1, and enforced a 60-second wall / 1-GiB sampled process-tree RSS bound. Helper total timeout was 55 seconds.

Actual version commands both exited 0:

```text
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
```

The checker ran `lake --no-cache build +YulangClosure.CallbackHygieneCorrespondence`; **build succeeded, 2 jobs, exit 0**. It then invoked the generated audit with `lake --no-cache env lean -j1 -M1024 --root=<task-local-temp> <task-local-temp>/YulangProofAudit.lean`. During pretty-printing of the fifth theorem's type, the outer guard observed process-tree RSS over 1 GiB and terminated the checker, which killed its active Lean subgroup.

- Audit start: `2026-10-29T19:42:13.609528+00:00`.
- Wrapper/checker exit: `130`; final Lean command exit: `-9` after termination.
- Elapsed: `8.063953784003388` seconds; peak sampled aggregate RSS `1109495808` bytes.
- Stop reason: `process-tree RSS exceeded 1 GiB`.
- Raw log SHA: `bd95bb5cb08c1a8151f2096098e3cd3444a568a0b15aa358bc72cc9c3aee207e`; resource/sample receipt SHA: `774829a9c74472d73dc75079dcd35c72a139d01aae5d65cfedb3630c17e46816`.

The module build succeeded, but the helper never completed its all-name validation. Complete type/axiom output exists for the first four names only: checked_use_inversion has `[]`; checked_catch_inversion, checked_catch_installed_arm and checked_catch_port each have `[propext, Quot.sound]`. The partial fifth type and interruption remain in the unmodified raw log. The other eighteen names have no complete audit block from this attempt; they are not represented as fully audited.

## Actual audit 2 — complete checker PASS

Luna's pushed R26 amendment 01 (`b8188a01545e98190776b277dd051949943b41b9`, provided ACK) authorized one final audit with an external RSS guard of 1,342,177,280 bytes. Amendment file SHA `e5a0b0b90843c71eca1a87ac43a155e007c05b4bf79b6ad0ba3b6fc9122f752a` was verified. It changed no source, theorem, toolchain, assignment bound or audit count. The audit-1 wrapper/log/resource files remain unchanged. A separate `run_bounded-audit2.py` applies the amended guard; its SHA is `cb768268ab93f95abc19cd390dd8c6b9eff081740d2dce643e3a707985dc3479`.

Exact full audit-2 argv are `lean-scratch/audit2-command.json` (SHA `e2c93527f6154c7f7abfe685dfa569088fc324b81b06de325dae69b569ced8e3`) and `.txt`; all 22 theorem flags are unchanged. Wrapper wall cap 90 seconds, checker total timeout 85 seconds, same explicit project/native Lake and unchanged checker SHA. Native Lean still runs `-j1 -M1024`; CPU 0, task-local TMPDIR and no Cargo overlap. Module, dependency and toolchain hashes remained exact. Actual versions again match the version strings above.

Audit-2 selected module build exited 0; generated theorem audit Lean command exited 0; full checker exited **0** after validating all 22 ordered complete audit blocks and printing PASS for every requested declaration.

| Attempt | Start UTC | Exit | Elapsed seconds | Max sampled tree RSS bytes | Stop |
| --- | --- | --- | --- | --- | --- |
| 1 | `2026-10-29T19:42:13.609528+00:00` | 130 | 8.063953784 | 1109495808 | Original 1-GiB guard |
| 2 | `2026-10-29T19:47:09.021119+00:00` | 0 | 6.799220432 | 1121263616 | Complete PASS, below amended guard |

Combined audit elapsed time: **14.863174216 seconds**, two of two attempts, below 120 seconds. Audit-2 raw log SHA `51c21b52961953482b7ef4a4e110947d502adf98d91e14bf60e5883e015e2b67`; resource/sample receipt SHA `d3a906f91efaf0548ad3060ddb476f607db2d5f3f0f273926a2311a03578c77e`. Audit-1 resource failure is retained separately and is not relabeled as a pass.

Complete exact printed types and full axiom lists for **every** requested fully qualified name are preserved in `lean-scratch/audit2.log`, extracted verbatim to `complete-types-and-axioms.txt` and structured in `complete-audit.json`. No accepted block is inferred from a source grep. The actual union is `{propext, Quot.sound}`; no `Classical.choice`, project axiom, `sorryAx` or native-evaluation assumption occurs. All 22 declarations were verified by the checker as theorem declarations.

## Parent application and remaining premise

No authenticated R26 native records were supplied to this leaf. No concrete History witness or source-derived invocation/receipt/Grant instance is constructed here, and no runtime return is claimed. The model's `CatchReady` remains explicitly a lower-level guard; callback PortReady checks stored entry/Name/use/execution joins, while the RootComp branch still lacks native image/receipt reachability. Even a completed audit would leave native Grant, complete Flow/Path, source/arm ownership, observer freshness and exact record-to-History correspondence for both unchanged source routes open.

The candidate generated_selection_actual/history_conserved chain can supply actual-event and exact consumer-coordinate facts after an authenticated History witness exists. companion_event_fresh/companion_emit_actual/commit_preserves_other_event can supply a distinct-event residual clause. Their complete type/axiom audits now pass. Their mathematical premises still require independent source-native evidence; this handoff does not promote them for source/native application. Original parent §5 still needs a joint source-admissible strategy at the original scopes and lawful independent allocation.

Represented: static annotations, invocation-instantiated permission, typed entry/Name/use/receipt coordinates, current and historical executions, owner-minted request events, installed Catch/arm identity, callback/computation branching, companion lineage and distinct lifetime transitions. Omitted: ModuleRun/closed-primitive path, full image/receipt/Flow-Path interpretation, symbolic rows/wildcard/release, operation type arguments, full owner-stack validation, replay and all-source typing. These are model omissions, never restrictions of the original accepted source domain.

No fresh independent review is claimed; review and any resource-seam disposition belong to Luna. No Cargo, Git, descendants, compiler/source-fixture edits, manifest/toolchain edits or root imports were performed by this leaf.

## Complete per-theorem axiom census

All names below have prefix `YulangClosure.CallbackHygieneCorrespondence.`; exact complete types are in the verbatim artifacts above.

| Theorem suffix | Complete transitive axiom list |
| --- | --- |
| `checked_use_inversion` | `[]` |
| `checked_catch_inversion` | `[propext, Quot.sound]` |
| `checked_catch_installed_arm` | `[propext, Quot.sound]` |
| `checked_catch_port` | `[propext, Quot.sound]` |
| `permission_preserves_actual` | `[]` |
| `emit_conserved` | `[propext]` |
| `commit_conserved` | `[propext, Quot.sound]` |
| `step_conserved` | `[propext, Quot.sound]` |
| `history_conserved` | `[propext, Quot.sound]` |
| `empty_conserved` | `[]` |
| `emit_events_before` | `[propext]` |
| `step_events_before` | `[propext, Quot.sound]` |
| `generated_events_before` | `[propext, Quot.sound]` |
| `generated_selection_actual` | `[propext, Quot.sound]` |
| `empty_inflow_rejected` | `[propext, Quot.sound]` |
| `companion_event_fresh` | `[propext, Quot.sound]` |
| `commit_preserves_other_event` | `[propext]` |
| `commit_removes_selected_event` | `[propext]` |
| `companion_emit_actual` | `[]` |
| `shallow_discard_preserves_contributions` | `[propext]` |
| `normal_return_deactivates` | `[propext]` |
| `lifetime_branches_distinct` | `[]` |

## Changed/generated paths and cessation

Only the four R26 output leases were written: the repaired module, its `.lake`, `isolated/ep-hygiene-r26/lean-scratch`, and this handoff. Source module SHA remains `0621f43739c12ce1e7919a50de129414a4748d8359bf46740babd69f4854011e`. Selected `.olean` SHA: `9e6ba6cd8c96ead734247fd4d07ec39f8afae1cb10b4e5ac729787bb401f90ce`; the complete selected-module generated-file inventory is `lean-scratch/generated-artifacts.json`. The source contains no proof holes, project axioms or checker bypass; complete kernel/axiom verification above supplies the acceptance evidence.

Scratch contains the unmodified checker, original/amended resource wrappers, both exact command files, theorem list, both raw logs and resource samples, repair/statement-preservation receipt, four separately preserved audit-1 blocks, complete audit-2 type/axiom artifacts and artifact hashes. No R24/R25 bytes, compiler code, fixtures, expected outputs, toolchain/manifests, root imports, central task/status or Git state were written. No descendants were created. No tests/default whole-project build were run.

Finalization: `2026-10-29T19:48:55.249834+00:00`; conservative active interval from actual receipt: 496.250 / 600 seconds. Both audit processes exited; **writes and all processes are stopped after this handoff**. Next owner is Luna's independent reviewer and the Rust/source lane for authenticated records and the remaining native-Grant/RootComp/History premises. No budget renewal or audit 3 is requested.
