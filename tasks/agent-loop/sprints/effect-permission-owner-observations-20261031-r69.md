# R69 contract — construct endpoint observations from one owner

Sprint: `EFFECT-PERMISSION-OWNER-OBSERVATIONS/20261031-R69`, revision 1.
Baseline: pushed R68 checkpoint `18a27477985618f8002d1efa7de1af0382cd0862` on `origin/yulang3`.

## Objective and fixed outcome

Continue the unchanged Rust/Lean effect-hygiene goal. R68 proves endpoint equations only after receiving a finite `Owner` containing `views`, component-position/term/component/live-component tables, and current value/effect representative vectors. R69 must construct that Owner from one source-owned observation table and the complete semantic-fact Term seed closure. Do not accept the R68 Owner as a free input and do not introduce `FaithfulExtraction`.

**Rust:** in `crates/yu-solver/src/candidate_receiver.rs`, add a private borrowed endpoint-observation view derived from the same `InventoryPackage` / `InferenceSession` consumed by R68. It must connect all `SemanticFact` lower/upper Terms to `inventory_term_views` and its complete recursive child closure; preserve original arena-branded Terms and ordered view/child coordinates; and retain the complete owner component-position, component-Term, component, live-component, value-representative and effect-representative tables from that same session. Reification consumes this view or its checked source-derived records. Missing terms, rows, positions, stale representatives, foreign identity or checked-conversion/allocation failure must fail explicitly through the existing private gap channel; preserve `SearchLimit`. No inference, routing, subtraction, permission-consumption or execution changes.

**Lean:** new `notes/theory/lean/YulangClosure/OwnerEndpointObservationsR69.lean`. Define primitive owner-table inputs and a constructor for the R68 `Owner`; do not take `Owner` itself as input. Prove complete fact-Term seed coverage under recursive view children, exact lookup agreement for every constructed table, component round trips, namespace preservation, current representative agreement, and composition with R68 endpoint decoding, R67 qualified selection and the same R66 slot-0 / slot-2 reads. Theorems must expose their primitive table and successful-read premises. No source-authenticity predicate, universal faithfulness axiom or supplied interpreted inventory may stand in for construction.

The packet proves that a constructed mathematical Owner is coherent with its primitive tables. The exact primitive observation encoding's correspondence to actual Rust object identity, arenas and execution remains OPEN unless directly established; never claim whole-package source/native closure from an independently supplied finite table.

## Falsifiers and review gate

Reject the claimed agreement if a fact Term or recursive child is omitted; a view or component row is substituted; a foreign branch/session is mixed in; component position/term/component/live row fails round-trip; either namespace loses or aliases a representative; or a current representative is stale. Preserve repeated FactIds and all table rows. Fresh independent review must inspect Rust construction completeness before accepting Lean composition.

## Exact leases

- Rust author `/root/r69_rust`: `crates/yu-solver/src/candidate_receiver.rs` and `tasks/agent-loop/inbox/effect-permission-owner-observations-r69-rust.md`.
- Constructive proof author `/root/r69_proof`: `notes/theory/lean/YulangClosure/OwnerEndpointObservationsR69.lean` and `tasks/agent-loop/inbox/effect-permission-owner-observations-r69-proof.md`.
- Read-only independent reviewer `/root/r69_review`: `tasks/agent-loop/inbox/effect-permission-owner-observations-r69-review.md`.

Only the primary edits `current.json`, sprint/admission/launch/outcome/state archive, stages explicit paths and commits/pushes. Workers cannot start subteams. No overlapping writers.

## Immutable inputs

- R68 Rust `candidate_receiver.rs`: `46f952a233c7e15c062e4009ad1baf0c37badec9c2a0b3406141627afae71bc6`.
- R68 Lean `SemanticFactEndpointInterpretationR68.lean`: `4359d461015d61851ba3951c028eaca8607abe00cac52ffcaba3ba2f3fee5693`.
- R68 Rust handoff: `dd06cb5d372f632442ab150bd58acf3c68eaf80f7d854bc8775d947ca72ba0ab`.
- R68 proof handoff: `eb9525d6d5836bdaa2ec73899e299962dfdf2282051c66a02a876e13ebae1086`.
- R68 independent review: `39fc894efeb39b59036a5722e1b093cae89d2d00f87acadf9900258859181269`.
- R68 outcome: `70e6705709c41f413c7f95a4939563dc2408e0a4d0f5edfaf7aed31fa56ba52e`.
- Direct Rust owners `lib.rs`, `candidate_context.rs`, `yu-hir/src/module.rs`, and `term.rs` are pinned in the R68 handoff; rehash and record them before editing. R65/R66/R67 dependencies remain the exact hashes recorded in the R68 handoff.

If any direct pin differs from the admitted checkpoint, stop before editing and report it.

## Verification, resources, and remaining gates

Fresh cap **6,000 seconds**: Rust 1,400; proof 2,200; review 1,200; primary 1,200 including 500 closeout; Astra 0. Use the same checkout and pinned Lean 4.35.0 stdin audit (`-j1 -M1024 --stdin`), retaining full theorem types and transitive axiom reports. Run `git diff --check` on exact leased paths. No Rust builds, Cargo, tests, formatter, Lake, cache, target, scratch, new worktree, environment, dependency or configuration changes. No large capture/output. User-directed WSL cleanup remains binding.

A bounded R69 PASS is not original A/B closure, full source/native correspondence, native resource/failure equivalence, actual successful native Runs, whole-language effects, soundness, principality, termination or production authority.
