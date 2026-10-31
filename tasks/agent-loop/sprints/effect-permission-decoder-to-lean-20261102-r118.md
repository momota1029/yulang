# Sprint EFFECT-PERMISSION-DECODER-TO-LEAN/20261102-R118 — decoder success into R116 inputs

Status: admitted continuation of the unchanged Rust/Lean soundness and effect-hygiene goal. Preserve the original source quantifiers, accepted semantics and all parent gates.

Branch / baseline commit: `yulang3`, `43f2536806481feb073a4f5a39ce00b7edc650fe`.
Authority: `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2; original parent `YulangClosure.SourceProblem.InferenceSoundness`, `notes/theory/lean/YulangClosure/Contracts.lean:128–130`; whole closure scope `docs/yulang-whole-proof-closure-ja.md` §§1,3–4.
Dispatcher: `/root/r114_dispatch`, selected R118 after R117 closeout. R117 outcome: `tasks/agent-loop/history/effect-permission-native-decoder-20261102-r117-outcome.md` SHA-256 `95e6206a28f909a4cfffc303248ccf99602140b1ebc3ad0661eba772c2242a46`.
Contract revision 2; SHA-256 recorded in current-state/admission receipt after freeze. Revision 2 adds the explicitly user-requested bounded Rust integration analysis below; the original Lean lane and its frozen outputs are unchanged.

## Fixed outcome and success evidence

Take the frozen R117 revision 2 decoder success checks and construct the strongest honest Lean result connecting them to the existing R116 `selected_endpoint_member` and `internal_certificate_member` inputs. Keep native endpoint coordinates `(view, member)`, decoded operation family, formal registration, packed permission storage position, and state/batch owner distinct. The theorem must derive membership from the actual modeled owner-view read and exact retained permission record; it may not assume permission membership, a generic “faithful decoder” proposition, or an equality of unrelated numeric namespaces.

Required outputs: `notes/theory/lean/YulangClosure/NativePermissionDecoderR118.lean` and `tasks/agent-loop/inbox/effect-permission-decoder-to-lean-r118-proof.md`. The handoff records original theorem statements, fully qualified candidate declarations and premises, construction equations, omitted cases, complete unproved Rust-to-Lean premises, parent application, static inputs and STOP receipt.

Success is either (a) a concrete conditional Lean construction whose exact premises follow from independently identified R117 guards and which derives the R116 endpoint/certificate membership conclusion, or (b) a source-grounded obstruction naming the first exact field/read/branch that cannot supply an R39, R45 or R54 premise. A field-to-field table alone is not success. Do not define the source domain by the candidate model or promote an abstract record model as actual Rust behavior.

## Parent scope, reuse and open premises

Original inference soundness remains `∀ s x d a, supported s → generates s x d → solves d a → ∃ e, sourceJudgment s x e ∧ sameScoped s x e a`. The annotation policy permits subtraction of a listed concrete effect but does not impose a closed input row; extra effects such as `write` remain outward. No claim in this packet closes original soundness, effect hygiene, principality, termination, R114 admission transport, source/native correspondence, Rust integration or production.

Reuse only the pinned candidates below. R116 has theorems `selected_endpoint_member` and `internal_certificate_member`, with explicit `prepare`, `permissionFor`, `SelectedSource`, operation-match and R45 `extract` premises. R45 retains all exact source/native owner reads. R54 requires equality of the full owner including state and batch. R117 revision 2 was statically accepted but remains unapplied and uncompiled; its successful observer path is not yet an authenticated operational interpretation into these Lean records.

## Immutable inputs

- R117 patch `c3858b35433433806e7f8a01f27c12ab5491a8116e6e88c2b1e32a6ccf5beab1`.
- R117 Rust handoff `6557b368fb1f092d5c4151cb54d74c7dd61c92153105e8720b17189c1efd128e`.
- R117 independent review `a47cfe5a54cc2d22b3fcd2834bed3f3c959ba85cfcb28cf38ed095db06488664`.
- R116 Lean `SuppressionPermissionR116.lean` `2aed350468964d90d8d83714177fff77d477e3df0846ae23150194bd76270e3a`.
- R39 `ComputationPermissionEntryR39.lean` `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e`.
- R45 `InternalPermissionIncidenceR45.lean` `9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f`.
- R54 `OwnedResidualProjectionR54.lean` `cc5d0b01485560e5091ce454b066ca2fc41eb350eee24ae525133a13bed401c9`.
- Rust baseline `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`, exact four owner blobs and hashes in the R117 contract.

## Lanes and boundaries

1. Registered `lean_prover`, ≤480 seconds, Luna-authorized exact writes to the Lean candidate and one handoff above only. Build no executable Rust/native oracle and add no assumed bridge that bundles the missing source interpretation. No descendants.
2. Fresh independent `compiler_referee`, ≤180 seconds, read-only review of frozen Lean artifact, R117 patch/handoff/review, and pinned R39/R45/R54/R116 sources. Attack unrelated-index collisions, foreign permission/registration, different state or batch, same family with distinct operation identity, native `(view,member)` versus family confusion, missing R39/selected-source premises and theorem-scope narrowing. Write one review receipt only.
3. Primary adjudicates, updates compact current state and records. Original Lean sprint ceiling ≤900 seconds; Astra 0.

## User-directed Rust integration analysis (revision 2)

The user explicitly asked to analyze the Rust implementation and push the result. Add one bounded static lane, without changing the R111 execution gate:

1. Registered `implementer`, ≤300 seconds, reads only immutable baseline `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`, R117 patch/handoff/review, and exact R111/R113 contracts, frozen handoff, review and outcome artifacts. It may reconstruct the R111 target and overlay R117 hunks in memory. Do not read or write any dirty working-tree Rust source, including `candidate_receiver.rs`; do not touch `candidate_scheme.rs`, runtime files or quarantined paths. Do not apply a patch or create source/index/cache/worktree/temp output. Write only `tasks/agent-loop/inbox/effect-permission-rust-integration-r118.md`.
2. A fresh independent `compiler_referee`, ≤180 seconds, reviews only those same frozen inputs plus the frozen Rust integration handoff and writes only `tasks/agent-loop/inbox/effect-permission-rust-integration-r118-review.md`.
3. The primary may push the reviewed analysis and records as a research checkpoint. It must not stage or push Rust source: R111's compile gate is still blocked by the documented aggregate-storage cap and no configured remote verification facility. Do not repeat resource/environment probes or create storage environments. If the frozen inputs yield no new integration fact beyond R113, stop without duplicating its analysis.

The revision-2 Rust lane adds at most 480 seconds, making the combined cap ≤1380 seconds including the original ≤900-second Lean sprint. Existing per-lane caps are unchanged; no extra primary budget is authorized. No Cargo/compiler/build/test, Lean/Lake/checker, patch application or Astra work.

Execution: no Lean/Lake/checker, compiler, Cargo/build/test, patch application, formatter, toolchain lookup/install, environment/resource exploration, cache, worktree or scratch path. R108's missing hard aggregate Lean output cap and R111's Rust execution cap remain unchanged. Candidate declarations remain CONSTRUCTED/UNCHECKED. Do not repeat feasibility probes.

R117 Rust patch remains FROZEN and research-only; no further Rust source/patch edits absent a concrete proof/review inconsistency and a primary-granted exact revision lease. Independent reviewer and worker stop receipts are required before closeout. Only the primary stages explicit reviewed paths and pushes the exact coherent outbound range.
