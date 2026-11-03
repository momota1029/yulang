# R307 proof handoff — revision 1

Sprint: `R307`; contract SHA-256 `983a347b741551dc3f14dea45ce19f424d8bf0710d9d252961de045cb9678c06`.
Baseline: `ef1b11a91`. Assignment/author: `/root/r307_apply_proof`, registered lean_prover leaf; no descendants. Runtime session/model/effort metadata were not supplied to this leaf and remain UNKNOWN. Primary launch message establishes this assignment; no independent review is claimed.

Outcome: **checked finite source-incidence construction and conditional parent application**. Original whole-source, EI-All registration/interpretation, R159 semantic closure and production gates remain OPEN.

## Governing claims and exact mapping

Read `AGENTS.md`, base operating invariants, `rules/goal-driven-sprints.md`, selected contract, Lean skill and its source/execution references, and proof-portfolio guidance. Original claim: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §1, preserving every supported source, original scopes and one shared witness; not narrowed by this fixture. Apply ownership corrections: `notes/design/2026-10-10-parent-copy-scc-intrusion.md`, Apply-result source-fragment ownership, Nested Apply membership and Definition-root Value ownership. Group syntax in this packet establishes no new semantic Value adjacency.

Original SG manuscript: `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` §§2, 3.1–3.3, 5.2, relative to genuine L1–L5. Source-call construction: `notes/progress/2026-10-06-source-call-generation-construction.md` §§1–3 and its explicit P/A limits. Authoritative complete result: `notes/design/2026-10-24-computed-call-result-constructor.md` §§2–5, especially independent arms and EI-All formation. Source syntax/correction notice: `docs/yulang-source-type-safety-ja.tex`, opening 到達点と訂正 and `sec:source`; research drafts add no semantic authority.

Exact Lean inputs: `OriginalSourceOwnerReification.TableToSource.app` (existing signature unchanged); `SourceAppAdmissionR159.app_admission_iff` (existing signature unchanged). Prefix for every new declaration below: `YulangClosure.OriginalSourceApplyIncidenceR307`.

`AppIncidence` checks emitted Apply-row membership, actual definition owner/root, parent physical row, raw callee, full Group.inner route and argument physical occurrence. Full node refs retain local source index, HIR occurrence ordinal, source-key ID, locator and form. `PhysicalJoin` additionally joins the same execution's key table. The old owner table has no source-key ID field, so the new key table join is explicit rather than pretending the old locator alone is native identity.

`app_table_to_source` uses the original constructor with independently supplied child reifications. `owner_incidence` concretely discharges the finite joins; `owner_application` supplies the existing genuine child reifications. `owner_input_exact` proves emitted source equals old owner-table input. Both children and Group are retained.

`table_app_admission_iff` and `owner_parent_edge` use the unchanged R159 consumer. They are equivalences with **all original semantic premises still on the right**, not proofs of source typing. Incoming `Inputs`, `RuntimeReadout`, `LocalAdmissions`, original kernel, environment and Context are arbitrary; the single occurrence/data/state and exact candidate extension are shared by all locals and both children. No InterfaceModel, chosen catalogue, desired EI meaning or successful child judgment is used to force closure.

## Parent edge and exact remaining premises

Before: `TableToSource.app` independently translated children without authenticating their raw Apply edges.
After: exact emitted finite owner/application/raw callee/argument joins and Group path are checked, and that exact tree is passed to original `TableToSource.app` and R159.

For the unannotated concrete fixture the annotation premise list is empty. First open concrete semantic input is `decode readout environment = some state`. Then an actual occurrence/logical payload must satisfy `admissions.logical state ⟨coordinates.physical .application, .viewLogic, 0⟩ .viewLogic data`. At the **same** `environment.extend` using that candidate, all original App locals must hold: descriptor formation, whole argument compatibility, complete Call certificate, source Call incidence, callable image, conditional role/initial-call origin, value check (callee returned value → descriptor), computation check (callable image → synthesis), and both child SourceJudgments. Responsible owner remains primary/source-semantic and source-construction lanes; this extractor does not observe the caller Context or these facts. EI-All complete independent arm inputs, actual EI interpretation, q_c registration, original checking/admission and whole source/native refinement remain open.

## Frozen data and direct dependency hashes

Changed Lean artifact SHA-256: `c3f63a454831d4193ee708f754d4d1194ececfa5a21d777624556eacb0898a07`.
No root import was edited. Changed tracked paths are only that module and this handoff.

| Input | SHA-256 |
| --- | --- |
| OriginalSourceOwnerReification.lean | `95d9749ce93ecfc82d6423ba193a261f2725178a7e62cea469b57ae316af3d7e` |
| OriginalSourceOwnerReificationTrace.lean | `b9a15df005c730db27fc385c58ca07b433f1095f017e0969155106da7478fb0a` |
| OriginalSourceOwnerReificationInstance.lean | `3aab685323e00b69cb9c21d847582e442590e0ff5e810fab50662b7d9127f887` |
| SourceAppAdmissionR159.lean | `5e948a1f8a3aab66028f885ebf16b6ffeed81999039e8a5a4e9c3caf84464408` |
| SourceLogicalOccurrencesR104.lean | `0e7a42d66578388585a5abd1da12c77a9d7d46823687ed511d26e359b3078f39` |
| frozen extractor source | `ebb1ee47bf5e76f8414dbf0145c96373b8e5a4394885924f6b24e32b0e2649c1` |
| owner.lean / owner.json | `27fb71cb057980f32c827ddc591cf72846dd646649452f554abf322291ca116d` / `be165e5b49f258ad8b4cd1dbaf106879d83eeedbdf036c78acaa26980acb5a11` |
| nested.lean / nested.json | `c4d12693cc0b53f2a16ef43f63091e640ae2a2b3aecb23f584aab07ae2ba7733` / `007205b277fea9178f66aa74be4c63eef74b5998b2f2bfe081573dc780197fae` |
| empty.lean / empty.json | `d52bbe0f26bbba7f4a3a3a0e3b0840d9e97f7845f7ee772666ff55819be69f60` / `f555b9eb996657123b9276727ea608fc2c0eb0e4e7bf08ceb0829f8420c3f614` |

The three generated `applyIncidences` declarations were copied verbatim. Same-run JSON key rows were projected into `SourceKeyRow` records. Copy verification and complete source/data hashes are in `/tmp/yulang-r307-proof/fixture-copy-check.log`; frozen originals are preserved in `/tmp/yulang-r307-proof/fixtures/`. No finite fixture proves general Rust–Lean equivalence. The previous owner output had an extra LF; it was rejected for exact-input use and regenerated by the source owner before this final proof.

## Actual verification and complete axiom results

Resolved installed native Lake using `elan which lake`, with no installation/update. Exact executable: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
`lake --version`: Lake 5.0.0-src+eb6cafb, Lean 4.35.0. `lake --no-cache env lean --version`: Lean 4.35.0, x86_64 Linux release, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

All cache/build writes were isolated under `/tmp/yulang-r307-proof/lean` (a copy of the pinned project, no dependency changes). Import command `lake --no-cache build +YulangClosure.OriginalSourceOwnerReificationInstance +YulangClosure.SourceAppAdmissionR159` completed 36 jobs; raw log `import-build.log`. Direct checks `check-01.log`, `check-02.log`, `check-04.log` succeeded. `check-03.log` preserves three actual Decidable synthesis failures for the opaque `ExactApply` definition; repaired by explicitly unfolding it before `decide`. The enclosing diagnostic shell in that attempt exited 0 because it ended with `cat`; that shell exit is not a successful Lean receipt.

Final bundled checker command and every theorem argument are retained in `/tmp/yulang-r307-proof/audit-command.txt`: helper with isolated `--project`, absolute `--lake`, `--module YulangClosure.OriginalSourceApplyIncidenceR307`, all 18 authored `--theorem` entries and `--timeout 120`, with TMPDIR inside the lease. **Exit 0**. Named-module build: 37 jobs, exit 0; audit Lean invocation: exit 0. Full printed types, theorem-kind checks and all transitive `#print axioms` results: `/tmp/yulang-r307-proof/audit.log`, SHA-256 `89e18368fb0b4eeaa3bdcfad1bc4d3c2563615ee8d0767b370aa0f180b3e1aba`. This was a focused module audit; default/full integration build remains the primary's choice. No changed-module warnings. One replayed baseline warning at `SourceLogicalOccurrencesR104.lean:152:70` (unused simp argument) is outside this leaf's lease; primary owns its disposition.

| Declaration suffix | Complete axiom list |
| --- | --- |
| `group_path_retains_group` | `[]` |
| `app_table_to_source` | `[]` |
| `table_app_admission_iff` | `[propext, Classical.choice, Quot.sound]` |
| `owner_input_exact` | `[]` |
| `owner_parent_join` | `[propext]` |
| `owner_callee_join` | `[propext]` |
| `owner_projection_join` | `[propext]` |
| `owner_argument_join` | `[propext]` |
| `owner_incidence` | `[propext]` |
| `owner_application` | `[propext]` |
| `owner_swapped_children_rejected` | `[propext]` |
| `owner_missing_group_rejected` | `[]` |
| `owner_swapped_reification_rejected` | `[]` |
| `owner_ungrouped_reification_rejected` | `[]` |
| `nested_computed_callee` | `[]` |
| `empty_shared_key_distinct_occurrences` | `[]` |
| `empty_conflation_rejected` | `[propext]` |
| `owner_parent_edge` | `[propext, Classical.choice, Quot.sound]` |

Source search in changed/module direct owner/R159 dependencies found no proof holes or bypasses; matches for `admitted` and existing axiom-audit commands are not declarations of axioms. The transitive audit, rather than the search, establishes the reported axiom lists.

## Coverage, resources and stop

Represented concrete owner tree: resolved names, nested Lambda, raw Group, App, ordered block and existing declaration. New nested fixture retains all three Apply rows and proves the computed callee is the second emitted Apply. Empty fixture proves Apply/Unit have equal source key/position/range but distinct occurrences and local indices, and rejects occurrence conflation. Both direct row swaps and swaps at AppIncidence are rejected; Group removal is rejected both at raw-path and actual reification levels. Nested and Unit fixtures are **raw-incidence evidence only**: the old fixed `PhysicalKey`/`LocatedExpression` schema has no arbitrary-node/Unit construction, and has not been silently expanded or substituted for whole-source coverage. Original general source syntax and parent scope remain unchanged.

Grant: 2400 seconds; no children, Git, compiler edits or scheduling writes. One Lean process at a time, pinned `-j1 -M1024`, final helper total timeout 120s. Final audit was coordinated after primary confirmed the Cargo review build had completed. Scratch footprint 207 MiB; aggregate CPU/RSS were not measured. Only exact leased paths were written, including the isolated copy, fixture snapshots and logs beneath `/tmp/yulang-r307-proof`.

Writes stopped after this revision. No subprocess or descendant remains active. Ready for fresh primary-assigned independent review; not self-certified, integrated or production-approved. Next in-scope action belongs to primary: review this frozen module/data join and route the exact remaining semantic/registration obligations to their owners.
