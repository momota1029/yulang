# R146 proof lane — boundary-deviation receipt, conclusions withheld

## Frozen assignment receipt

- Sprint: `EFFECT-PERMISSION-NATIVE-INCOMING-STATE/20261102-R146`.
- Assignment / handoff ID: `effect-permission-native-state-correspondence-r146-proof`; revision **1**.
- Contract: `tasks/agent-loop/sprints/effect-permission-native-incoming-state-r146.md`, amended bytes SHA-256 `870b2d7e4756ca61231d1c7720298d067fe41abef5f15f521c53af4ee0ed190a`.
- Admission bytes observed after the stop instruction: SHA-256 `9152b13a3565c79f426a17cfbe81b55f9666c43b5556df8ba95230ee786a628b`. A later primary correction is not authenticated by this hash.
- Baseline: immutable `3560df97dab02744da10e897c73c1cf94118f4ee`.
- Author / worker: `/root/r146_native_state_proof`, current R146 assignment; no descendants or coauthors.
- Requested routing: current-state row says `registered prover` / `role default`. General leaf guidance prefers Sol/high; that preference is not observed launch metadata. Effective model and effort: **UNKNOWN**. The initial runtime message incorrectly described Sol/high as the packet request; the worker corrected this explicitly to Luna before freezing.
- Exact sole output lease: this file. No other artifact, scratch or generated output exists from this assignment.
- Outcome class: **provisional procedural receipt; substantive source/proof conclusions WITHHELD; NO VERDICT**.

## Deviation and stop

Before Luna recorded the narrow input amendment, I read baseline `candidate_effect.rs` bodies while tracing the requested actual effect/Catch consumer. The original relevant-files list did not include that file. I treated it as directly relevant to the original consumer question without first returning the input expansion to Luna. That was an input-boundary deviation. All these reads used committed baseline Git objects; no working-tree Rust source was read.

Pre-amendment `candidate_effect.rs` body ranges printed to the worker were **1–185, 260–330, 1180–1278 and 1380–1410**. They include declarations, the Catch-operation builder, and the effect-view remapping helper. Baseline-qualified pattern searches also returned matching lines from this file, including test-source lines; none were executed. A pre-amendment source-wide locator search also exposed the out-of-scope **`candidate_extrusion.rs:1147` function-name line `candidate_apply_effect`**, alongside the previously admitted caller locator `candidate_context.rs:4290`. This locator was returned to Luna before requesting the narrow input amendment; its early exposure belongs in this deviation inventory too. No `candidate_extrusion.rs` body had been read at that point, and no `candidate_receiver.rs` body was read at any time.

After the amendment arrived, a read of `candidate_extrusion.rs` printed **1140–1172**; its requested upper line was 1337, beyond the file length, so the Python display loop then raised `IndexError` and exited 1. Later reads printed `candidate_effect.rs` **1437–1546 and 1274–1291**, plus `candidate_source.rs` **1604–1654**. The 1437–1546 display also exposed the neighboring annotation-variable/hole declarations after line 1506; I do not claim those neighboring declarations were reached effect operations under the amended scope.

I notified Luna that the admission's initial assertion that neither added body had been read before amendment was false for `candidate_effect.rs`. Luna then instructed: stop all source inspection; withhold substantive conclusions from the pre-amendment read; return a boundary-deviation receipt; no further `candidate_extrusion` review or verdict. I acknowledged that instruction immediately and performed no further source inspection. Only control-document hashes and the clock were read afterward.

All interim source/mathematical conclusions sent in runtime messages are **unaccepted producer observations and withheld from this handoff's result**. They must not be used as reviewed evidence or parent-premise closure. This receipt neither retrospectively authorizes the early reads nor independently adjudicates their acceptability.

## Complete read inventory

All source searches were explicitly baseline-qualified `git grep`; source displays were `git show <baseline>:<path>`, directly or through a read-only Python subprocess. Python range displays loaded the complete immutable blob into process memory before printing the listed ranges. There was no extraction to a file, cache or scratch directory. Some combined tool output was truncated; the inventory records the requested displays, not a claim that every requested line was visible or semantically audited.

| Baseline source | Body displays requested before amendment, inclusive lines |
| --- | --- |
| `candidate_scope.rs` | 1–282 |
| `candidate_context.rs` | 1–245; 270–308; 2920–2994; 3170–3318; 3390–3458; 3790–3878; 4420–4490; 3807–3839; 3900–3928; 3950–3982; 4200–4277; 4450–4486; 3455–3504; 4690–4726; 4280–4310 |
| `candidate_source.rs` | 160–343 |
| `candidate_scheme.rs` | 4440–4490; 4730–4820; 4865–4909; 628–643; 1025–1035 |
| `shadow_apply.rs` | 1294–1332; 1640–1663 |
| `candidate_effect.rs` | **1–185; 260–330; 1180–1278; 1380–1410 — pre-amendment deviation** |
| `candidate_intrusion.rs`, `lib.rs` | Baseline-qualified matching lines only; no body display |

Post-amendment body displays are listed in the deviation section. `candidate_receiver.rs` appeared only as the path and matching comment line 2922 in a baseline-wide `ScopeState`/protection locator search. Its body was not opened. `candidate_effect_kernel.rs` was proposed in coordination but never read or created.

Pattern searches covered transformer/state/evaluation symbols, FreshUse/remapping, scoped-flow/demand, replay/composition, effect allowance and Catch/operation symbols. Searches over `crates/yu-solver/src` also returned test-file matching lines. The only repository-wide enumeration was immutable `git ls-tree -r --name-only`; later enumerations were restricted to theory/design/inbox paths. No source content was searched in the working tree.

Proof/source documents read from baseline: full `NativeScopeTransformer.lean`, full `NativeFreshScopeTransport.lean`; `NativeScopeFreshMapR145.lean` displayed lines 1–27, 114–130, 157–182 and declaration-locator matches; full R145 source/proof inboxes; full compose construction and compose authority; original preservation note §§1, 3, 5 and its header; birth-level correction §§2–6 and its header; Lean README first 65 lines; pinned toolchain, Lake configuration and manifest.

Working-tree control reads: root `AGENTS.md`, `AGENTS.pre-sprint.md`, proof skill and its source map, design-authority rule, top-level inference principles, goal-driven sprint rule, agent-loop README/current state, selected contract/admission, and R145 outcome. These were read only; central records were not edited.

## Parent and proof status

The assigned parent is R145's actual incoming-state/shared-FreshUse-map application premise, under the unchanged compose source contract. The original A/B preservation statement remains quantified over every supported original source program/history, actual extrusion pairs and original joint scopes/witnesses, with the birth-level correction. No source restriction, new state model, substituted premise or production change was introduced.

**No parent application is claimed.** The authentic consumer, accumulated prefix, empty observer input, deferred demand and `use_instance` correspondence require a clean admitted source audit. This interrupted lane supplies no accepted answer to that question, no reachable source counterexample and no proof of an omitted rename.

No theorem was constructed or checked. Relevant declarations were read as source only: `YulangClosure.NativeScopeTransformer.evaluate_then`, `evaluate_rename`; `YulangClosure.NativeFreshScopeTransport.fresh_evaluate`; `YulangClosure.NativeScopeFreshMapR145.evaluate_rename_on_support`, `fresh_evaluate_on_support`. Their actual inferred types and complete axiom dependencies are **NOT_RUN / UNKNOWN** here. R145's seven theorem candidates remain unchecked. Historical receipts, declaration text and Python/Git success are not kernel acceptance or source/native refinement. This receipt does not reuse any historical proof as a discharged source premise.

## Frozen input hashes

SHA-256 hashes below are for complete immutable baseline bytes, not working-tree source:

```text
4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03  crates/yu-solver/src/candidate_scope.rs
a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905  crates/yu-solver/src/candidate_context.rs
bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49  crates/yu-solver/src/candidate_source.rs
e2b6209e3bf486a302e52e5051be60bf7cd8187a7a1e8453087b94f77e06b814  crates/yu-solver/src/candidate_scheme.rs
102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01  crates/yu-solver/src/candidate_effect.rs
80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61  crates/yu-solver/src/candidate_extrusion.rs
475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97  crates/yu-solver/src/candidate_intrusion.rs
2fa42a5570e660babab5da6361e0d71e0c022b234a21f7e01b78eafbfc65f278  crates/yu-solver/src/shadow_apply.rs
68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6  notes/theory/lean/YulangClosure/NativeScopeTransformer.lean
1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5  notes/theory/lean/YulangClosure/NativeFreshScopeTransport.lean
d47da744694beb04abfcf3b06137b5a04b241f568490af5fbf59147933a2db57  notes/theory/lean/YulangClosure/NativeScopeFreshMapR145.lean
773a1ed4c2ebe7503438c57a06acd23e03fbc1fd0d6ae30260848c4430fe676e  notes/theory/2026-10-15-compose-scoped-release-construction.md
fd56f819f9b33adc5d75cbfdae378c90903e4aa3a266fc053c05dda315d40679  notes/design/2026-10-15-compose-scoped-effect-release.md
da15341b46d3b7adef8cb1bd90d02bfe6dd27fc594a5fb96520f5cf84f82dcea  tasks/agent-loop/inbox/effect-permission-fresh-map-support-r145-proof.md
e543b1cd4c6d98d6fdaf912f228a8cd53e407fe72edf3338b2f1c9fca295ffba  tasks/agent-loop/inbox/effect-permission-fresh-map-support-r145-source.md
3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271  notes/theory/2026-10-13-intrusion-source-preservation-proof.md
ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae  notes/design/2026-10-24-birth-level-scc-intrusion.md
```

These hashes identify inputs and do not certify conclusions about them. Authors of reused artifacts are their original recorded authors; this worker authored only this procedural receipt.

## Resources, remaining owner and writer stop

No Lean/Lake/Rust/Cargo/tests/builds/checker, environment creation, dependency change, production edit, Git mutation, nested CLI, subagent, external contact or scratch/cache write ran. Read-only Git/Python/control-file commands and this leased write are the actual operations. One display command's `IndexError` is a read-script failure, not a compiler or proof diagnostic. Start time and total CPU/RSS were not instrumented; no exact elapsed-time measurement is claimed. The original 600-second cap was not expanded or reset; stop was directed by Luna. Clock observed immediately before receipt construction: `2026-11-01 02:43:47 UTC`.

Mutual TODO `R146-INPUT-BOUNDARY-DEVIATION-1`, owner Luna: reconcile the admission with this command inventory and select a clean admitted owner if the actual consumer audit should continue. Inputs are the amended contract and immutable baseline; proposed output is a newly leased source-correspondence result. Falsifier for any later consumer claim: an admitted real effect/Catch decision that actually reads a transported tag/protection state, together with its same-map transport, contradicts an absence claim. This receipt makes no such absence claim. Original incoming-state application, source/native correspondence, A/B and production stay OPEN.

Stop condition reached: **all source inspection stopped; all writes stopped after freezing this revision; no active continuation or descendants; no unresolved descendant leases**. The sole new path is this inbox file. Pending primary intake only; no independent review or integration verdict is supplied. Handoff SHA-256 is returned separately over these final bytes. Further source work requires Luna's assignment, not an autonomous continuation of this stopped packet.
