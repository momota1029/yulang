# R34 stage ledger — RuntimeProgram-owned HIR snapshot identity

Admitted with a fresh 6,000-second envelope: Rust 1,600; Lean 1,600; review 1,200; Luna 1,600 including 500 closeout; Astra 0. No R33 transfer. User's storage constraint is binding: existing checkout only; no worktree/copy/environment/build/cache/target/scratch/extraction.

## Objective and fixed semantic domain

Give candidate callback coordinates an owner token derived from the exact retained `Arc<HirModule>`. Arc clones denote the same immutable HIR snapshot and preserve the token; separately allocated HIR modules denote distinct snapshots even when structurally equal. The token retains the Arc allocation for its lifetime. No structural/Debug/index-derived token, numeric global counter, or cross-process uniqueness claim.

The only mutable compiler source lease is `tools/inference-playground/src/runtime/program.rs`. `machine.rs` and `receiving.rs` stay QUARANTINED under UNKNOWN_WRITER and are excluded from reads and writes. Integration into them is proposal-only.

## Exact assignments

| Stage | Owner | Exact outputs | State | Gate |
|---|---|---|---|---|
| Rust owner implementation | `/root/effect_permission_r31_rust` | `tools/inference-playground/src/runtime/program.rs`; `tasks/agent-loop/artifacts/native-snapshot-owner-r34.patch`; `tasks/agent-loop/inbox/effect-permission-native-snapshot-owner-r34-rust.md` | NOT_STARTED | Opaque token wraps exact retained Arc; clone equality and separately allocated owner rejection; no compile/build/runtime claim |
| Lean binding and application | `/root/effect_permission_r31_lean` | `notes/theory/lean/YulangClosure/NativeSnapshotOwnerR34.lean`; `tasks/agent-loop/inbox/effect-permission-native-snapshot-owner-r34-proof.md` | NOT_STARTED | Owner-bound decoder laws compose with R33 and R32 coverage/round-trip; exact types and complete axioms |
| Independent review | `/root/effect_permission_r31_review` | `tasks/agent-loop/inbox/effect-permission-native-snapshot-owner-r34-review.md` | NOT_STARTED | Starts only after both outputs freeze; inspect code and proof, adversarial Arc owner cases |
| Luna | `/root` | contract, manifest, admission, ledger, current, outcome | ACTIVE | Exact leases, live roster, hashes, adjudication, static check and closeout |

## Dependencies and receipts

R34 contract SHA-256 `e81a6b7316623bc009f6f1488fdf5d9ba6e258efe9e6144d164f5c81d1061ff2`; input manifest SHA-256 `57c07d14d9074a50e55c1b116c656599240883e61879b214f53448005da8e8ca`; admission receipt SHA-256 `3f8aa804dcb3d0dfb1659bef3aa60a729cd0f2d584fa4a0142678caed776c99e`.

Baseline branch/HEAD `yulang3` / `afd05a2aaec63890629d97a663a7aff54574075b`. `program.rs` baseline SHA `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907`; `yu-hir/module.rs` SHA `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`. R33 conditional module/review and R30 archive pins are in the manifest. Lean is pinned at v4.35.0 with source/authority pins in the manifest.

## Dispatch log

Admission is complete. Producers remain NOT_STARTED until Luna confirms exact-path runtime dispatch. No worker may start a build or create an environment. At producer freeze, record exact file hashes, audit results, elapsed bounds/UNKNOWN and writes-stopped receipts. Start independent review only after both producers stop writing.

## R34 producer dispatch

The synchronized collaboration roster confirmed `/root/effect_permission_r31_rust` and `/root/effect_permission_r31_lean` RUNNING after exact-path dispatch in session `R34-20261031`. Rust's only source write lease is the non-quarantined `runtime/program.rs`; Lean owns its standalone module and proof handoff. Reviewer remains NOT_STARTED until both freeze. Effective model metadata and aggregate active elapsed are UNKNOWN unless the runtime reports them. No build, test, worktree, copy, environment, target, cache, scratch, extraction, or quarantined path is authorized.

## Rust HIR owner binding frozen

Rust worker `/root/effect_permission_r31_rust` completed terminal with no descendants. `tools/inference-playground/src/runtime/program.rs` SHA-256 `9823cd8d5c972e0c6ec2766d66f9d21c6564727317bc2646d2480a9e85132f74`; proposal SHA-256 `36d96676c3c561bf2f525cd167ef33840221da4f2a93236b33932e70c9bc5361`; handoff SHA-256 `556d0ffda6e3c6d1f3b3e6722b0640564a72ff834be77cf632d1e293f061ea79`.

The source adds private `HirSnapshotToken(Arc<HirModule>)`, `identifies_same_snapshot` via `Arc::ptr_eq`, and a `RuntimeProgram` accessor that clones the capability. Both constructor paths funnel through the sole initializer; `_hir` and the token clone the same input Arc. A cloned token retains that exact HIR allocation; separately allocated HIRs compare foreign regardless of equal contents. Worker reports `git diff --check` pass; no tests, compilation, runtime, cache, build or quarantined consumer access. Aggregate active time UNKNOWN under the 1,600-second cap. Serializer use remains proposal-only and no production claim follows.

## Checkpoint Git capability

The local `.git` directory and index are not writable. The authenticated GitHub read confirmed remote `yulang3` still at baseline `afd05a2aaec63890629d97a663a7aff54574075b`. A scoped GitHub API blob-write attempt was rejected before object creation with `MCP tool call requires approval, but approval policy is never`; no remote commit/ref update and no local Git mutation occurred. Do not report R33/R34 as committed or pushed. Preserve all unrelated workspace changes; no broad staging.

## R34 local Git checkpoint and push

At closeout, exact R34 paths were added successfully, with no unrelated paths staged. The reviewed implementation/proof/artifacts and the CLOSED_PASS current state were committed as `90fd99073` (`feat: bind callback tokens to retained HIR`) on `yulang3`; `git push origin yulang3` succeeded, moving `afd05a2aa..90fd99073`. The earlier remote API denial above remains an accurate earlier failed attempt; the later local Git route succeeded. No force push or broad staging.

## Lean owner proof frozen

`/root/effect_permission_r31_lean` is terminal: STOPPED, writes stopped, no descendants. Module `notes/theory/lean/YulangClosure/NativeSnapshotOwnerR34.lean` SHA-256 `24ca25828e1a58f9c3246e5f50f2c73ba8ead6d2d003d05c8c2a8a3d2e85795a`; proof/audit handoff `tasks/agent-loop/inbox/effect-permission-native-snapshot-owner-r34-proof.md` SHA-256 `35c722635c09da36d28cee356032f92028d1d8d651f5e1bd959d51d68eee0bff`, 251,617 bytes. The 80,968-byte module preserves the exact 66,862-byte R33 prefix. Pinned Lean 4.35.0 stdin under read-only bwrap: exit 0; 76 theorem types and complete axiom reports captured; empty stderr and no diagnostics. Of 17 new theorems, 8 use no axioms, 7 use `propext`, and 2 use `propext, Quot.sound`. The measured construction/repair/audit/handoff interval is 505.634s; startup reads are unmeasured. Owner constructors establish fresh-owner separation without an inequality premise; clone/retention equality and complete-row/R33-to-R32 application are proved. This is a finite same-process retained-Arc model; allocator/Drop correspondence, serializer token transport, AST/annotation provenance, request/Grant/History and original A/B remain open. No build, test, cache, environment or scratch was created.

## Independent R34 review — minor patch artifact repair

`/root/effect_permission_r31_review` completed read-only and is STOPPED, with writes stopped and no descendants. Source-owner logic and the conditional Lean model PASS within the stated same-process retained-Arc scope. Independent pinned Lean 4.35.0 stdin audit passed all 76 theorem declarations, exit 0, no diagnostics, empty stderr, exactly matching the frozen complete types/axioms receipt; reviewer measured 3.289599456s for its subprocess, aggregate review time UNKNOWN. Across all 76 theorems: 17 no axioms, 29 only `propext`, 30 `propext, Quot.sound`. No `sorry`, `admit`, project axiom, `native_decide`, or bypass.

Minor artifact-integrity finding: `tasks/agent-loop/artifacts/native-snapshot-owner-r34.patch:47` declares hunk counts 7/8, but its body has 6 old and 7 new lines; the exact context `Some(dictionaries)` is omitted. Other three hunks have correct counts. Source is correct and needs no repair. Reopen only the proposal patch and Rust handoff to regenerate the exact source diff and update the patch hash; then obtain a fresh review of that artifact. No patch application, test, build, or quarantined access occurred. The reviewer confirms clone/retention identity, equal-content separate-allocation distinction, single constructor funnel, exact R33/R32 proof application, and explicitly notes that the Lean pool/history interpretation must correspond coherently to simultaneously retained native Arcs. Allocator/Drop semantics, cross-process identity, source-row authenticity, serializer transport, Grant/request/History, original A/B, hygiene/soundness/principality/progress/termination/production remain OPEN.

## R34 owner-diff artifact correction frozen

The Rust worker completed the authorized artifact-only repair, STOPPED with writes stopped and no descendants. `program.rs` remained unchanged at SHA-256 `9823cd8d5c972e0c6ec2766d66f9d21c6564727317bc2646d2480a9e85132f74`. The owner-diff section was regenerated from the exact read-only `git diff` and independently compared byte-for-byte with that command output. The quarantined proposal suffix remains byte-identical at SHA-256 `943054c4d2bf4ba24419ef41734f7cfc4f3cf87567b3f2930359b97640fad55d`.

Corrected patch SHA-256 `2e8de543a4c721d33a775102961c930b82754d47411ae6c4f3ec4ea39b2004c3`; updated Rust handoff SHA-256 `c3213be2469c6a91ee6d69221430a40a5cfe9826461d6fcd022717851666a1f0`. No source, test, build, patch application, cache, scratch or quarantined consumer access.

## R34 corrected-artifact delta review PASS

The same independent reviewer completed read-only re-review and is STOPPED, writes stopped, no descendants. The corrected owner-diff section exactly matches current `git diff`; all hunk counts match bodies (6/7, 6/18, 6/12, 7/8), `Some(dictionaries)` is restored, and the proposal suffix is unchanged at SHA-256 `943054c4d2bf4ba24419ef41734f7cfc4f3cf87567b3f2930359b97640fad55d`. Corrected patch and refreshed handoff hashes match the frozen artifacts: `2e8de543a4c721d33a775102961c930b82754d47411ae6c4f3ec4ea39b2004c3` and `c3213be2469c6a91ee6d69221430a40a5cfe9826461d6fcd022717851666a1f0`. `program.rs` unchanged. Reviewer confirms previous full source/Lean review remains valid. No new semantic claim; no Lean rerun, patch application, build, test, quarantined access or file write. R34 source-owner and Lean owner-model gates pass within scope; broader native serializer integration and parent obligations remain open.
