# R74 store lookup / R73 model correspondence — frozen revision 1

Sprint: `EFFECT-PERMISSION-STORE-HIR-LOOKUP/20261031-R74`, contract revision 1, SHA-256 `e20477f1fea775ca9bd2cadc32dfff883d03833a0a68d8d08974486c1d63c1c1`.
Assignment: `/root/r74_proof`, handoff revision 1. Author: this source-correspondence producer only; no descendants or coauthors. Requested Sol; observed model/effort UNKNOWN. Primary supplied the assignment and later authenticated the Rust author's STOPPED / WRITES STOPPED handoff before this final audit.

Objective/method: source-level case derivation for the selected `ConstraintStore` lookup and retained inventory coordinate, applied to the unchanged R73 finite Lean model. This is conditional correspondence evidence, not constructive theorem closure, independent review, Rust type checking, runtime evidence, or a fresh Lean acceptance receipt. No alternative language meaning is selected.

## Baseline and frozen dependencies

Baseline: branch `yulang3`, commit `21cf99c051dbca3450ef184396e43a01f8dae323`. R74 input manifest SHA-256: `12411b44a6fa42cd6f86030df9baf8318900ede3fc96ced3588b50afe0a0d676`.

| Dependency | Frozen SHA-256 |
| --- | --- |
| `crates/yu-solver/src/lib.rs` (R74) | `15e7b131a65f8476eec575d978dc629d15d49e72149325ef35a8c08acc8fc745` |
| `crates/yu-solver/src/candidate_receiver.rs` (R74) | `6452e18c32bd55e49b31a2dcd474d39140ca97b73ce71a0f4fede07d32b4840e` |
| `crates/yu-hir/src/module.rs` (unchanged) | `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646` |
| `notes/theory/lean/YulangClosure/OwnerExactCompletedInstanceR73.lean` (unchanged) | `afed53ee5ebb82bbe87c171c6ac2808919976046df4cb2e0fdeb774f618a6e87` |
| R74 Rust handoff | `9b4b5a1a5f3ba0c3bc2df06005a6882db74a4c6f376479816ce631e146382124` |

These hashes, the contract and manifest were re-read with `sha256sum` after Rust cessation. The manifest's pre-edit source hashes are `25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4` (lib) and `eb35c73ead829ed439a347d3cb665d52d3aa4b45b242c1155cfd4377a68d6415` (receiver). Their pre-edit equality is the Rust author's retained receipt, not my observation before editing. The receiver's checkout Git diff includes the already frozen, uncommitted R73 changes; it is not an isolated R74 delta. The Rust handoff explicitly enumerates the R74 delta. I did not recover and byte-compare the old uncommitted receiver independently.

Governing sections: R74 contract “Original outcome and success evidence”, “Permissions and resources”, and “Frozen seam and stop conditions”; R73 review “Blocking Rust finding” and “Lean result and R72 repairs”; `rules/design-authority.md` authority order and approval gate; `rules/research-lab.pre-sprint.md` one semantic baseline/source-evidence distinctions; `rules/git-concurrency.md` disjoint-file freeze; top-level inference principles §§1–4. Original A/B/source scope and R66 `Root` remain as pinned by R73. No inference, constraint-generation, propagation, execution or semantic change is authorized here.

## Exact local derivation

Let `H = store.hirs`, `M = store.occurrence_hir_positions`, and `Own(h,s) = h.owns_occurrence(s)`. With ordinary Rust `get`, `filter`, `map`, `or_else`, `enumerate` and `find` behavior, inspect `lib.rs:3897–3906`:

1. If `M[s] = i`, `H.get(i) = Some(h)`, and `Own(h,s)`, the accessor returns `Some((i,h))` immediately. The `h` is the borrowed `Arc` slot from `H`; the returned index is the very index used by `get`.
2. If `M` lacks `s`, its index is out of range, or the indexed artifact fails `Own`, the first chain returns `None`. The lazy fallback searches `H.iter().enumerate()` and returns its first owning `(j,h)`.
3. If no admitted artifact owns `s`, both branches return `None`. A misleading map hit cannot authenticate a foreign artifact because the indexed branch rechecks `Own`.
4. Therefore `lookup(s).is_some()` iff `exists j < H.len(), Own(H[j],s)`. `require_owned` at `lib.rs:3887–3895` has exactly this success predicate: indexed owning hit OR the same inventory membership scan. Its body is unchanged against the baseline Git source read during this audit.

This argument covers arbitrary finite inventory/map contents, including stale map positions and duplicate admitted entries. It assumes normal safe execution of these library operations; no compiler or runtime executed to establish that premise here.

Complete identity is retained: `module.rs:1438–1450` gives `HirOccurrenceId` equality as equal ordinal AND `Arc::ptr_eq` artifact tokens, and hashes both. `HirModule::owns_occurrence` at `module.rs:2103` tests the artifact token by `Arc::ptr_eq`; it does not compare ordinals, module names, content, or the `_serial` counter. Ownership does not add an ordinal-range check. Lean `Occurrence A` likewise retains artifact plus ordinal, while `requireOwned` tests artifact membership only.

Minimal symbolic discriminators (static derivations, zero executable probes):

| Inventory/map/query | Required result and discriminating reason |
| --- | --- |
| `H=[a,b]`, `s=(b,0)`, `M[s]=1` | indexed `Some((1,&H[1]))` |
| same `H,s`, map absent, `M[s]=2`, or `M[s]=0` | fallback `Some((1,&H[1]))`; last case rejects the wrong artifact before scanning |
| `H=[a]`, `s=(b,0)`, `a != b`, even `M[s]=0` | `None`; equal local ordinal supplies no membership |
| `H=[a,a]`, `s=(a,0)`, `M[s]=1` | indexed coordinate `1`; absent map yields first fallback coordinate `0`; no uniqueness assumption |

A foreign-session occurrence is rejected precisely when its artifact is absent from this store's inventory. Session provenance alone does not imply rejection: two sessions may admit the same artifact. That distinction is required by the accepted model.

## Coordinate and owner trace

`candidate_receiver.rs:1564–1582`: provenance supplies the full `cause_occurrence`; unchanged `store.require_owned` runs first. Existing occurrence rows are selected by full `HirOccurrenceId` equality. A new row obtains `(artifact_index, borrowed_artifact)` from this store's accessor and stores that exact `artifact_index` alongside the original occurrence reference. There is no secondary pointer scan or `InferenceSession` lookup. The returned artifact is not stored in the occurrence row; it remains recoverable at that exact store coordinate.

`candidate_receiver.rs:1052–1065`: validation obtains `artifact` using the retained coordinate from the admitted slice, obtains the store accessor's tuple, checks coordinate equality, full ownership and borrowed-slot pointer equality, then rechecks `require_owned`. The earlier owner/slice checks at `:936–942` bind that admitted slice to `experiment_owner.session.store.hirs`; `primitive_projection` at `:752–789` authenticates the selected experiment against the retained completed-view owner before reading its tables. Both new method receivers are `ConstraintStore`, where the method is now defined. Source inspection removes the previously identified missing-method premise; this is not a claim of compiler acceptance.

Lean namespace: `YulangClosure.OwnerExactCompletedInstanceR73`.

- `ExperimentRows` (`:338`) retains the selected store's admitted-artifact list. `requireOwned` (`:374`) is `s.artifact ∈ o.admittedArtifacts`.
- `Readbacks` (`:399–404`) requires complete selected-owner store/fact/provenance/representative equations, equal occurrence/position lengths, and for every zipped row `o.admittedArtifacts[row.2]? = some row.1.2.artifact`.
- `decodeOwner` (`:422–437`) selects the completed view, checks its experiment pairing, selects that experiment's rows, decides `Readbacks`, then invokes `decode`. Artifact sharing never bypasses the experiment/view pairing.
- `admitted_occurrences` (`:505`) and `owner_selected_readbacks` (`:439`) apply to an existing `OwnerDecoded`. They do not construct a Rust extraction or prove pointer equality. `shared_artifact_does_not_identify_experiment` (`:513`) explicitly permits two experiments to own the same artifact. `owner_r66_same_witnesses` (`:570`) still takes the genuine unchanged R66 `Root` and use/lambda coordinate premises.

Conditional correspondence hypotheses: (H1) interpret Lean artifact equality faithfully as native artifact-token pointer equality; (H2) extract `admittedArtifacts` from this exact store inventory, preserving order and duplicate positions; (H3) extract occurrences and their retained positions without alteration; (H4) authenticate experiment/view registries and all other complete readbacks to the actual selected Rust owners; (H5) retain the normal immutable-borrow and standard-operation behavior assumed above. Under H1–H3 and successful source validation, every extracted occurrence satisfies the coordinate conjunct of `Readbacks`, hence artifact membership/`requireOwned`. Under H4 plus the remaining decoder checks, the unchanged R73 successful-decoding theorems apply. The accessor repairs one source owner/coordinate premise; it does not establish H1–H5 or all `Readbacks` by itself.

The Rust validator additionally insists on the accessor-selected coordinate, while Lean permits any inventory coordinate containing the correct artifact. This is a stronger source acceptance check inside the modeled relation, not a claim of converse equivalence or global artifact uniqueness. Indexed selection among duplicates remains observable only as the retained internal coordinate.

## Evidence limits and next action

Static source case analysis is the method, with no random seed, enumerated numeric range, executable mutation, test oracle, or additional transition checker. The Lean definitions and source are separately read artifacts, but share the explicit identity/list-extraction assumptions above. They are not independent executable oracles. Deleting the indexed ownership filter would invalidate wrong-artifact rejection; deleting fallback would invalidate membership completeness; substituting a new scan's index would invalidate exact coordinate retention; collapsing artifact to ordinal or artifact to experiment would invalidate the selected identity contract. Those are logical discriminators, not executed mutations.

Commands: `sed`, `rg`, `nl`, `cat`, `sha256sum`, read-only `git show`/`git diff`, and `git diff --check -- crates/yu-solver/src/lib.rs crates/yu-solver/src/candidate_receiver.rs` (exit 0). All tool commands completed. No Lean/Lake/Cargo/compiler/build/test/formatter, cache, target, scratch, environment, dependency or Git mutation. Resource envelope: 450 seconds; exact CPU/RAM and active-work telemetry UNKNOWN. No descendant or background process was started. Only the assigned note was written.

R73's retained acceptance/axiom evidence was read, not rerun. Fresh Lean checking and imported-module integration are outside this packet. Actual Rust-to-Lean extraction, physical completed-view/experiment identity, admitted-Arc slot identity, pointer/slice/map/allocator correspondence, finite-width/resource behavior, genuine R66 `Root`, original A/B, whole-language hygiene/soundness/principality/termination and production remain OPEN. This note is an author contribution, not independent review. No local counterexample to the required frozen source path was found.

Recommended next action: primary supplies this frozen source/note/handoff set to the fresh R74 delta reviewer, retaining the compile/runtime and physical-extraction frontiers explicitly OPEN.

Worker state: **STOPPED / WRITES STOPPED** after this revision and its final hash/check receipt; no descendants or unresolved descendant leases.

## Commit packet

- Exact lease/changed path: `tasks/agent-loop/inbox/effect-permission-store-hir-lookup-r74-proof.md` only.
- Baseline SHA: `21cf99c051dbca3450ef184396e43a01f8dae323`.
- Changed dependency hashes: R74 lib `15e7b131a65f8476eec575d978dc629d15d49e72149325ef35a8c08acc8fc745`; receiver `6452e18c32bd55e49b31a2dcd474d39140ca97b73ce71a0f4fede07d32b4840e`; Rust handoff `9b4b5a1a5f3ba0c3bc2df06005a6882db74a4c6f376479816ce631e146382124`. Lean/HIR hashes unchanged as above.
- Claim/review: conditional source correspondence; frozen for fresh independent review, not self-certified or production-ready.
- Checks already run: direct frozen hashes and source trace; source `git diff --check` exit 0. No executable probes or theorem checking.
- Proposed one-line research checkpoint message: `research: trace R74 store HIR coordinates to R73 owner readbacks`.
- Shared-record deltas intentionally left for Luna/curator: record source lookup defect disposition only after fresh review; preserve accepted R73 finite model and all physical/native, Root and A/B OPEN boundaries; retain 32 pending items, UNKNOWN/quarantines, R24 capacity override and R72 unrefunded UNKNOWN time. No shared records changed here.
