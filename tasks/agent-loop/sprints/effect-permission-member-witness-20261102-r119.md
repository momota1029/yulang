# Sprint EFFECT-PERMISSION-MEMBER-WITNESS/20261102-R119

Status: admitted continuation of the user's Rust/Lean soundness and effect-hygiene goal. This packet constructs a narrowly scoped, unapplied Rust candidate and a conditional Lean witness lemma; it does not promote source or close parent obligations.

Branch: `yulang3`. Baseline for implementation: immutable `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`. R118 outcome: `tasks/agent-loop/history/effect-permission-decoder-to-lean-20261102-r118-outcome.md`, SHA-256 `8bdebd3c146678b6365789092daa909767c45e432de9e247a85c8cf62c98793b`.

Authority: user explicitly requested Rust implementation analysis and push. Dispatcher `/root/r114_dispatch` selected this bounded candidate after R118 exposed that post-state decoder membership does not reconstruct R39's PRE-constructor action. This packet avoids that historical-state obligation for the local membership fact by preserving the successful lookup position in the same retained permission vector. R39/source constructor provenance, original soundness, full hygiene, native correspondence and production remain open.

## Fixed outcome

Produce an unapplied Rust patch based on the reviewed R117 revision 2 candidate. Replace the permission vector's `.any()` existence check with an ordered lookup that retains the found `permission_member_index`; carry that index alongside the existing projection/request evidence; at consumption, read the same retained permission record's `concrete.get(index)` and check that entry against the provider family. Preserve the distinction among formal registration, packed permission storage position, and member index.

The proposal must leave inference, suppression decisions, failure paths and public semantics unchanged. Do not add unused evidence. If the current projection/request structure cannot carry the witness without a semantic change, report the first exact obstruction rather than broadening the patch.

Rust outputs:
- `tasks/agent-loop/artifacts/effect-permission-member-witness-r119.patch`
- `tasks/agent-loop/inbox/effect-permission-member-witness-r119-rust.md`

Lean outputs:
- `notes/theory/lean/YulangClosure/PermissionMemberWitnessR119.lean`
- `tasks/agent-loop/inbox/effect-permission-member-witness-r119-proof.md`

Lean result must construct membership from the exact successful ordered search and same-record indexed read; it may not assume membership or a generic faithful decoder. State precisely which actual-Rust interpretation premises are still unauthenticated.

## Frozen inputs

- R117 patch: `tasks/agent-loop/artifacts/effect-permission-native-decoder-r117.patch`, SHA-256 `c3858b35433433806e7f8a01f27c12ab5491a8116e6e88c2b1e32a6ccf5beab1`.
- R117 handoff/review2: `6557b368fb1f092d5c4151cb54d74c7dd61c92153105e8720b17189c1efd128e` / `a47cfe5a54cc2d22b3fcd2834bed3f3c959ba85cfcb28cf38ed095db06488664`.
- R118 Lean candidate/review: `2ebb7797c683b2bbf51d746f89d58d9abc4be66b5520fe6c0f4c6007a70d82ab` / `bee20cccf34f82388f5f68836e95865c1f878381c45f0fa7df7a95cce8d0ef7b`.
- R118 corrected Rust integration handoff/review: `edec3e3d1747b9b4c78ea6ce19c9cc19de9db1f1ac113e4001c230db9249fd2f` / `d82023743bd5fd0c47d5baf21082aaa702359c787acd8687cc2ebd15177551f5`.
- Exact source reads: immutable baseline `candidate_receiver.rs`; R117 patch payload; pinned baseline `candidate_effect.rs` only for existing record/projection types. No dirty working-tree source.

## Lanes, resources and hard boundaries

1. Registered `implementer`, ≤480 seconds, Luna/high. Read only the frozen inputs above. Write only the R119 `.patch` and Rust handoff. Do not modify/apply source, inspect dirty Rust files or quarantines, or write index/cache/worktree/temp artifacts.
2. Registered `lean_prover`, ≤300 seconds, writes only the R119 Lean candidate and proof handoff. Use only pinned R118/R117 artifacts and exact Lean module sources identified by the proof skill. No execution.
3. Fresh independent `compiler_referee`, ≤180 seconds, reviews the frozen Rust patch/handoff and Lean candidate/proof plus exact pinned inputs. Write only `tasks/agent-loop/inbox/effect-permission-member-witness-r119-review.md`. Attack registration-vs-storage-vs-member-index confusion, different retained records, empty/duplicate members, foreign owner/state, lookup order, failure behavior, and unsupported source interpretation.
4. Primary ≤240 seconds adjudicates, updates state and pushes the coherent reviewed research checkpoint. Combined cap ≤1200 seconds. Astra 0.

No Cargo/rustc/compiler, build/test, Lean/Lake/checker, patch application, formatter, environment/storage probe, cache, worktree, scratch, or mount. Do not create a verification environment or repeat R111 feasibility checks. R111's source compile gate remains BLOCKED; Rust and Lean candidates remain unapplied/CONSTRUCTED-UNCHECKED. Do not stage or push Rust source. Only exact reviewed research artifacts may be pushed. Preserve all dirty/quarantined paths and existing leases.
