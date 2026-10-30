# R37 — checked source-use inventory correspondence

Status: ADMITTED. Sprint ID: `EFFECT-PERMISSION-SOURCE-INVENTORY/20261031-R37`
Branch / baseline: `yulang3` / `ce922eed506e1471abe9a0f6823674da7ba55039`
Contract revision: 1. Authority: unchanged annotation-effect hygiene policy and R36 source-use gate.

## Original outcome and success evidence

Advance the unchanged effect-hygiene/source-use goal by discharging R36's exact open Rust/Lean extraction gap. The Rust API enumerates complete direct Name-as-callee Apply uses from a retained source expression vector using occurrence identities; Lean R36 models owner-indexed occurrences and indexed edges but does not prove the Rust vector enumeration or occurrence-to-index extraction. R37 must define a guard-faithful indexed inventory and prove it corresponds to the issued individual-use witnesses.

Success: (1) Rust checks/builds the occurrence-to-index map from the actual retained expression vector without silently collapsing duplicate occurrence identities; retains source-owner, coordinate, edge, Observe and R35 row guards; preserves inventory order and `Some([])`; distinguishes allocation failure from semantic rejection; (2) Lean proves lookup soundness, complete enumeration, order/multiplicity preservation and empty inventory against R36's individual issuer, with allocation success as an explicit premise where required; (3) pinned Lean 4.35.0 stdin audit captures every theorem type and full axiom set; (4) fresh independent reviewer reconstructs correspondence from pinned allowed files.

Falsifiers: duplicate identities collapse; an invalid unrelated callee edge escapes checking; matching use is omitted or reordered; `Some([])` becomes failure; allocation failure is presented as a semantic negative; Lean assumes a generic Rust simulation law.

No user semantic, source-domain or production-authority change. Do not touch `Instruction::Apply` or either quarantined runtime consumer. No build, Cargo, Lake, tests, target/cache, worktree, copy, extraction, scratch or new environment. Existing checkout and pinned Lean stdin under read-only bwrap only.

## Exact lanes and leases

Rust implementation: only `tools/inference-playground/src/runtime/program.rs` and `tasks/agent-loop/inbox/effect-permission-source-inventory-r37-rust.md`.
Lean proof: only `notes/theory/lean/YulangClosure/SourceUseInventoryR37.lean` and `tasks/agent-loop/inbox/effect-permission-source-inventory-r37-proof.md`.
Fresh independent review after both freezes: only `tasks/agent-loop/inbox/effect-permission-source-inventory-r37-review.md`.
Primary only: this contract, manifest, admission, stage ledger, outcome and `tasks/agent-loop/current.json`.

Proof lane: build an explicit finite expression/index relation and guard-faithful two-pass inventory; prove source owner validity, completeness/soundness, order/multiplicity, and empty case; apply result to R36 parent and state precise remaining extraction premises. Rust lane: inspect only manifest paths; implement checked extraction while preserving R36 behavior; freeze hashes and stop before review. Each assignment may spend at most 1,600s. Review 1,200s; Luna 1,600s incl. 500s closeout; aggregate 6,000s; Astra 0. No transfer.

The direct range ends at source-planned inventory. Runtime Name receipt/entry/invocation/Grant/Catch/propagation and original A/B or whole-language claims remain OPEN. Unauthorized R36 quarantined-read incident remains recorded; preserve both quarantines and do not inspect them.

## Stop / integration

Stop at a source-owner or allocation-semantics gap not derivable from manifest inputs, any falsifier, budget bound or user stop. Freeze outputs, run only the pinned Lean stdin audit, obtain fresh independent review, synchronize central records, exact-path stage, inspect every outbound commit, and push a coherent reviewed range. No worker may commit or broaden a lease.
