# Sprint contract — MODULE-SUPPLIER-NATIVE-CORRESPONDENCE/r1

Status: ACTIVE. Baseline `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`. Selector admission after PAGEPACK r3 review pass. Fixed outcome: derive the fieldwise `ModuleDef → DefinitionUse → routing → receiving/export` chain only within the 18 accepted immutable pages, compare it with adopted `ModuleEnv-Expose*`, and identify the first remaining premise for each named supplier. Package acceptance is transport evidence only; do not treat it as a semantic premise.

## Authority and exact pins

- Accepted review receipt `tasks/agent-loop/inbox/module-supplier-native-slices-r3-page-pack-review.md`: `2accece307d35ccc8dfb67fd171fa24a3a37d62a16d7cc6b56934e07acad998c`.
- Accepted outcome `tasks/agent-loop/history/module-supplier-native-slices-page-pack-review-20261028-r3-outcome.md`: `679e182608764dbc1e4f4e5c9048062c5985fd204c3cb190c3594fe32b414a5f`.
- Manifest `tasks/agent-loop/sprints/module-supplier-native-slices-r3-pages/manifest.json`: `6c2c9fe80b294518b6ea8c8995e28a1b2604c3bb5e43f28e301c388219eb2c0a`.
- Generator `tasks/agent-loop/sprints/module-supplier-native-slices-r3-pagegen.py`: `e2990124a88099298abc5279a751c68ab87fefb2d066b5831bc59ff6bc249202`.
- Consumer `tasks/agent-loop/sprints/module-supplier-native-slices-r3-pagecat.py`: `4b50306376d8bafb187d400db7d683a6abdcb0aebfec6341c28e58804d63a6c7`.
- Governing source-slice contract `tasks/agent-loop/sprints/module-supplier-native-slices-20261028-r1.md`: `6ab211856d460e4c31fdcadd0f4c0576444444630eb9bcd380a53e4aec7f7435`.
- Adopted rule authority `notes/design/2026-10-17-module-environment-exposure-definition.md`: `d5d03de8b80eb2792cc35690f3fc3c871f9704f4aee8df815bce40b1f49f9d4d`.
- Adopted candidate source `notes/theory/2026-10-17-module-reference-materialization.md`: `f1971e53ef62a5b3d94897ca9774d67c021d21524d9774b14439748a00fee9eb` (use only clauses selected by the adopted authority).
- Existing authoritative module-expression owner `notes/design/2026-10-16-module-expression-source-owner.md`: `ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5`.
- Draft-only limitations, not authority: entry provenance contract `notes/design/2026-10-17-module-entry-provenance-contract.md` SHA `44f33397a45f5d17a0302c6b1efbfe1f7bbdf018caed2ece2acc18176a746bd9`; accepted-call HIR admission draft `notes/design/2026-10-17-accepted-call-hir-admission-contract.md` SHA `2f3b6dbb6e735b3c5da96f0bbdaa8357f7580435999e08136ce24e1bf19174ab`.
- Prior r4a2 source handoff `tasks/agent-loop/inbox/effect-permission-module-materialization-r4a2-source.md`: `e219b4210ba24fd97d15b128be67ae07242e6d34acca8a5bdede32d25ffb1e1e`; independent review `tasks/agent-loop/inbox/effect-permission-module-materialization-r4a2-review.md`: `46abd3d08ee0c98f2605a56a7ed59f5ec5080405e459219c457c59c7309542cd`; outcome `tasks/agent-loop/history/effect-permission-module-materialization-20261028-r4a2-outcome.md`: `e9ffa93b51c84be579f9653e094835a454d2b6ffcd9b7a79abad527dde2ae252`. Reuse as bounded history/coverage only, not implementation evidence.

All four exact owner pins and 18 page hashes are authenticated by the accepted review. Reauthenticate the exact artifacts assigned to each lane. No new owner or raw-source path is admitted.

## Goal, method and claim boundary

For each step, name the producer, stored identity/components, validator/branch guard, consumer, and exact equation supported by the admitted page. Trace `ModuleDef target → DefinitionUse → target/use components → selected routing branch → captured/freshened receiving value → owner export`. Identify the first unsupported equation and its owner for both `ModuleNameSourceTypingAndAdmission` and `ModuleUseReceivingExportCorrespondence`.

Distinguish open-use routing from captured/freshened incoming routing; actual `CandidateInference::export` from observer `CandidateDefinitionUseRef`/`definition_use`/`receiving_export`; native identity evidence from typed source entry, exact occurrence lookup and admission. A missing runtime certificate alone does not refute correspondence if the adopted mathematics supplies the premise; equally, structural target identity, routing success, observer traces, or port presence do not establish it. Preserve both suppliers unless all their complete premises are directly discharged. No generic assumed interface, circular supplier premise or auxiliary theorem may substitute for the bridge.

The adopted rule requires actual `E0`, prior `D_pub`, simultaneous `Reg(C)`, actual incidences `I_C`, lawful dependency-preserving `theta_C`, resulting `Gamma_C`, exact occurrence lookup preserving the actual Published/Family/Mono/Alias/Live constructor and whole map, plus branch-specific use/admission. Preserve original quantifiers, source domain, shared witnesses, callback → Call result → tuple `left`, A/B, complete Call/effects, N-Transport, F1/FK1 and all parent/native/production gates as OPEN unless direct reviewed evidence discharges them. `DELTA_AUTH_UNRESOLVED / NO_SAFE_CODE_SLICE` remains binding.

## Lanes, leases and outputs

**Source — Luna primary, 350s.** Read only the 18 accepted page bodies through the pinned r3 consumer and the above already-admitted authority. Reuse primary's authenticated governance coverage from the reviewed r4a2 source record. Produce a fieldwise source/native inventory with precise page/hash/line locators and first unsupported edge per supplier. Exact output: `tasks/agent-loop/inbox/module-supplier-native-correspondence-r1-source.md`.

**Proof — resume registered `lean_prover`, 300s.** Reuse that proof identity's own authenticated governance coverage and reauthenticate its prior handoff pin. Independently compare the same accepted page chain to the adopted rule; provide a sourced derivation or exact first unsupported equation and owner. No Lean/Lake invocation, theorem or axiom claim; no code edits. Exact output: `tasks/agent-loop/inbox/module-supplier-native-correspondence-r1-proof.md`.

After both freeze, a fresh nonauthor `compiler_referee` review (200s) checks every claimed edge against exact pages/rule clauses, owner/component joins, route direction, actual versus observer export, supplier circularity, source admission and bounded conclusion. It must reject any unsupported assertion. Primary records frozen review at `tasks/agent-loop/inbox/module-supplier-native-correspondence-r1-review.md` and an outcome receipt.

Read only the accepted page package and pinned admitted material above. Each page output <=4096 bytes; no source-owner expansion or direct reads of unadmitted paths. No tests, builds, Cargo, Lean/Lake, Git, children other than the assigned proof/reviewer, source edits, expected-output edits, probes or background work. Any required uncovered dependency is a STOP/escalation point, not implicit admission.

## Resources and closure

Full fixed charge **1,000 seconds**: source350 + proof300 + review200 + primary100 + contingency50. Current cumulative **5,700/7,200**; full charge leaves **500 seconds**. No refunds or reuse. Keep separate lane coverage/charges and record unknown startup/runtime. At closure both suppliers and all parent/native/production gates remain OPEN absent direct reviewed closure. Selector consultation is required at material contradiction, uncovered dependency, budget boundary or sprint end.
