# NATIVE-FRESH-USE-VALIDATION/r1 — Rust implementation handoff

Status: implementation bytes frozen; validator is partial source evidence only. No theorem, source/native closure, production permission, or independent review is claimed.

## Assignment and runtime

Contract: `tasks/agent-loop/sprints/native-fresh-use-validation-20261028-r1.md`, SHA-256 `fa16e84d3bd7cdb3c134bbc798c5bfd47e8af0686b80b961c7a8f49a692cf4f8` (matched before candidate source inspection). Requested role/model/effort: implementer / Luna / high. Observed model and effort: UNKNOWN. Current-session ACK sent to Luna before implementation. Active work began after all contract pins matched. Spent budget is bounded by the 500-second grant; no renewal requested.

Exact writes: this isolated `candidate_scheme.rs` and this handoff only. No tests, build, Cargo, Lean, or Git were run. No scratch/generated path was created. Writes are stopped and both paths are frozen for intake.

## Source change and correspondence

In `candidate_scheme.rs`, added `#[cfg(test)] InferenceSession::validate_fresh_use_graph` immediately before `freshen_candidate_graph_retained`; the successful `freshen_candidate_graph_core` path invokes it after preparation and before restoring bounds or extracting `fresh.terms[graph.root]`. An existing positive/negative Variant capture test calls it on two independently prepared FreshUse maps.

The validator reads immutable `Graph.nodes`, shared tuple/record/variant slices and captured rows, then reads actual `TermView`s from `self.store`. It checks every node index, including the graph root, constructor, polarity, four ordered Function ports, tuple order, record field name/optional/value, variant tag/payload order, and shared child identity. Leaf and row nodes are checked against their actual native views. It does not seed expected reconstruction from the retained root slot. EffectOperand is read through `effect_operands`, never treated as a term slot: bottom/empty atoms, effect-row images, contribution effect+origin payloads, and allowance/support/annotation view owner, position, allowed members, tail and operation declaration/occurrence are compared. Tail rows are checked against the shared fresh row vector.

Additional checks reconstruct role and field-tail obligation row ordinals from captured row keys; check evidence-map length and native captured-snapshot/imported-ID readback; compare attachment-bundle key coverage and copied bundle source fields; and check scope-region copies preserve their per-region scope/input maps. The independent proof's source map is `Graph` / `Node` / shared slices → `FreshUse.terms` plus `FreshUse.effect_operands` and `FreshUse.rows` → `TermView`/candidate context readback. Rust does not independently establish graph-to-original-source allocation authenticity.

## Coverage boundary and falsifiers

All seven Node variants have explicit branches. Unsupported shape, missing child/map entry, wrong polarity, reordered or changed child, altered sharing, wrong metadata, invalid row, unmatched effect payload, changed obligation index, evidence mismatch, bundle mismatch, or inconsistent copied region fails with `ReceiptMismatch`; there is no wildcard-success branch.

The validator does **not** yet establish the complete scoped relation transformer/demand rewrite, context-use/context-remap construction, or context-remap's relation to every renamed context root. Scope checking covers copied region shape and the region→scope/input maps, not an independently reconstructed full ScopeInventory allocation history. Attachment bundles are checked for copied source payload equality, but not the full relation incidence/consumer behavior. Effect operation provenance compares declaration pointer and occurrence; its private retained-byte accounting is not compared. The added test invokes the validator on two unmutated Variant cases; no mutation falsifier was added in this packet. These omissions mean the admitted complete validator goal is not closed.

Prior evidence reused: selected-module freshening proof handoff `tasks/agent-loop/inbox/selected-module-entry-freshening-reconstruction-proof.md` established the exact missing native equation and explicitly rejected `terms[root]` as an independent Phi. Reused source pin `33235b840c42be38be1df634291e309c0d143fa62f412afa633768be9b40aa0e`; its owner history already contains separate Variant/Record/Tuple readback tests. I did not reuse those assertions as proof of complete map validation. No Simple-sub bypass was restored.

Remaining authenticity premise: a source-grounded account of captured Graph allocation and all retained maps, including the unresolved scoped/context projections, must connect to the original source instance and the Lean native interpreter before the original parent or effect-hygiene obligation can advance. Original parent, effect hygiene, source/native and production gates remain OPEN.

## Frozen artifact hashes

- Pinned source baseline `isolated/selected-module-entry-freshening-repair-r1/crates/yu-solver/src/candidate_scheme.rs`: `33235b840c42be38be1df634291e309c0d143fa62f412afa633768be9b40aa0e`.
- Final source `isolated/native-fresh-use-validation-r1/crates/yu-solver/src/candidate_scheme.rs`: `6e0695e14895e4c9a0f44c6184586716780bdbdcdca8f52ff8663c2d4138101e`.
- Final handoff hash is returned with this frozen submission; no post-freeze edits are planned.
- No scratch files exist.

Next in-envelope step: Luna should freeze these bytes and have the independent proof/review lanes decide whether to extend the exact open scoped/context cases under the already authorized contract or report the validator gate OPEN. Do not promote this partial observation as a closed gate.
