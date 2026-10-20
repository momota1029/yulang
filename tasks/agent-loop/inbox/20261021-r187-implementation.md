# R187 Luna implementation handoff — rev10 trailing-separator repair

- Owner: Luna primary and sole Git integrator.
- Candidate rev8: `tasks/agent-loop/sprints/post-lambda-age-and-option-b-sequences-20261021-r187.md` SHA-256 `f0f511d1af5df9f3748e92a2d60601331c177b570e4feac20311069b4e6af652`; design SHA-256 `09593cd9967ff512147cbb83d01ca4421549030280de5054fc03c572ddd586d7`. Rev8 exact malformed-else delta review was CLEAN.
- Base implementation checkpoint: `facc59222326cedbf12c9cd4ff7dc171d2290ecf`, pushed to `origin/research/simple-sub-intrusion`.
- Independent static review of that checkpoint was NOT CLEAN: parser-produced terminal `BlockStatementSeparator` caused nonempty braced sequences to be rejected. It affects newline-before-close and explicit trailing semicolon.

## Repair

`sequence()` now rejects only an empty statement list. Separators still must alternate with valid direct `Statement` nodes, so duplicated separators and malformed item shapes remain rejected. The existing malformed-body HIR refusal test remains. The leased HIR test now records the explicit trailing-semicolon case; the multiline regression records newline-before-close.

Changed paths:
- `crates/yu-hir/src/module/local_source.rs` `7d45e98690551f81f7b18e1778a934c65c43c8e17ed06bff110877b86bf5f14a`
- `crates/yu-hir/tests/conditional_local_source.rs` `5e8e66511cebfa90189656e9a209e88d6b9ada83cd9ba8fb2fe8e4212f4fbf0f`

## Verification and limits

Previously: isolated `cargo check -p yu-solver` passed; isolated `cargo test -p yu-syntax if_` passed 31/31. After user resource direction, no additional builds/tests/execution were run. Scratch `target` cleanup: `cargo clean` removed 1236 files / 1.3 GiB. HIR, CLI, runtime, Web and end-to-end verification remain incomplete. New HIR case is unexecuted.

Next: fresh static review of this repair, preserving execution stop and existing leases. Parent theorem/A/B/source-native/production gates remain OPEN.

## Repair review receipt

Fresh static review of commit `58af75437808e1a53de001c5fe17d10e7cbb9b3a` returned CLEAN. It confirms valid terminal newline/semicolon separators are accepted after nonempty sequences while empty, leading/repeated separators, adjacent statements, malformed child shapes, and recovery-bearing bodies remain rejected. This review performed no execution. The HIR regression for explicit `;` and all runtime/CLI/Web checks remain unexecuted under the user's resource direction.
