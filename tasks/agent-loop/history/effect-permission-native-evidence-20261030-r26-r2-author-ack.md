# R26 R2 Rust author ACK — bounded observation repair

Status: **ACKNOWLEDGED BY LUNA; effective for dispatch after this record is pushed.** This is a sequential continuation of R26 under the approved amendment 02.

## Authenticated inputs

- Base contract `tasks/agent-loop/sprints/effect-permission-native-evidence-20261030-r26.md` SHA-256 `8b2fcc72995472465b23fc397f257d07a035b0b1ba15f8f62ee31ae705dc11e5`; base inputs `tasks/agent-loop/sprints/effect-permission-native-evidence-20261030-r26-inputs.json` SHA-256 `ec31c06563e6835101647272ce46930be55230481862621d8757b1193387e97d`.
- Active amendment `tasks/agent-loop/sprints/effect-permission-native-evidence-20261030-r26-amendment-02.md` SHA-256 `72c9bb96cf5e651dcb8a551bbffb8ad5b2477def0d0a1ab354469cc051acdd7b`.
- Observation schema `tasks/agent-loop/sprints/effect-permission-native-evidence-20261030-r26-schema-r2.json` raw SHA-256 `e767fb0c71752691c4ca953621105a1c7a1f4b3f5809423a71c30588d2d1a5ee`, canonical SHA-256 `118319c84980812e0a2bf5f5f4c968ddd4fba2fd08cdac0a65ca841510c0f9e7`.
- Inputs R2 `tasks/agent-loop/sprints/effect-permission-native-evidence-20261030-r26-inputs-r2.json` SHA-256 `2c6f136c1e498de2cfdc71a49deff4371822b0582cf5e84d411c46137c92a44c`.
- R1 rejected candidate archive `tasks/agent-loop/history/effect-permission-native-evidence-20261030-r26-r1-candidate-snapshot.tar.gz` SHA-256 `94a81f34e37b7418809cf1b4f618e8d060f7afbd52231388649b80df938b85ef`; its five archived members were independently verified against the frozen R1 hashes, and `build-target` was absent. Do not edit or replace the archive.

## Exact author packet

Author: `/root/effect_permission_hygiene_r24_rust`, same existing assignment and requested Luna/high settings (effective observed settings remain UNKNOWN). Resume only the six existing Rust paths below; no new path, dependency, worker or capacity. They are mutable R2 output paths only after this ACK is pushed and the author is dispatched:

- `isolated/ep-hygiene-r26/project/tools/inference-playground/src/runtime/machine.rs`
- `isolated/ep-hygiene-r26/project/tools/inference-playground/src/runtime/receiving.rs`
- `isolated/ep-hygiene-r26/project/tools/inference-playground/src/runtime/program.rs`
- `isolated/ep-hygiene-r26/project/receipts/hygiene.json`
- `isolated/ep-hygiene-r26/project/build-target`
- `tasks/agent-loop/inbox/effect-permission-hygiene-r26-rust.md`

For at most **400 seconds**, implement and freeze the additive R2 test-only observation repair. Record the actual `TemplateNode::Owner` transition (template/node, original/control-resolved/previous/selected owner, borrowed/fresh disposition, and existing OwnerOpen identity when fresh). Capture the actual retained outer receiver/control chain separately from the inner suffix, preserving frame identity/order. Join the resumed continuation through the real owner-resolution event and connect the retained write Catch/request through the outer chain. Keep response value/view lineage independently joined to the same write request. Preserve all prior mutation families and exact route results.

Keep all observer/validator changes under `cfg(test)`; do not change owner selection, control resolution, freshening, receiving/grant operations, production code, source semantics, fixtures, expected outputs or dependencies. The archived R1 snapshot is immutable. Stop and report if any extra source/path/dependency/schema meaning or semantic change is required.

This ACK grants **only source repair and freeze**. No Cargo, Rust compiler, test, formatter, Lean, Lake or checker command. After freeze, stop for a fresh independent exact-hash review (remaining precompile review slice at most 170 seconds); no compile without that ACCEPT. Runtime requires its own later ACCEPT. The frozen Lean result remains conditional and is not reopened. No Git operations by the author.

Resource ledger before dispatch: Rust 463/1,500 charged, 1,037 remaining; this packet cap 400 seconds, within both total remainder and the prior resumed packet's remaining 627 seconds. Review 313/1,000 charged, 170 seconds remain in the current precompile slice. Luna upper-bound charge recorded as 2,200/3,600 seconds, with 1,400 remaining and 500 reserved for closeout. No capacity reservation or path lease was released.
