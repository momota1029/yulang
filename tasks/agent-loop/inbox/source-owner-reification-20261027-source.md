# Implementation handoff — source owner reification (r5)

## Assignment and frozen inputs

- Sprint: `SOURCE-ORIGINAL-OWNER-REIFICATION-20261027/r1`, contract r5, SHA-256 `6c6b0de7d4d8f5259308d3aae6abd8aa1574b162ff06ed3e5b2375b32a260c0c`.
- Baseline: `a5d1e79ee`.
- Frozen schema consumed: `notes/theory/lean/YulangClosure/OriginalSourceOwnerReification.lean`, bytes 0–13698, lines 1–292, SHA-256 `266e169aaef8e79c41103fecdc7edae939d9059f49edde2e52ac39ffba4a769e`.
- Corrected implementation source: `tools/inline-authentic-extraction/src/bin/original_owner_reify.rs`, SHA-256 `49dd489ba29d215a9d6b562ce907c09bbc31dc2d645b02d4c81ee36a2b35b6d4`.
- Direct inputs checked before run 2: package Cargo.toml `21c64b4a22318a1ae89c346357161812a6ac313b6f0c4999853272cf73e2832b`; Cargo.lock `2ee467b8f6416aa7dda36f96f3401a0b0ae24a739ff7c6a2efccc1323777ee91`; existing `src/main.rs` `fc22f1ab490e815a800a6b1e91eb4ea978006d6956ac838329cddf7b09ad1472`; syntax/HIR files matched their r5 pins. Luna separately confirmed all 18 governing pins before authorizing run 2.

## Result and boundary

The adapter source compiles and contains checks for the fixture's actual HIR definition root, parse-owned definition key, local-source occurrence/source-key/range joins, exact inline binder-token origins, same-root parameter resolutions, raw Apply callee Group edge and projected child, actual argument, and ordered statement/final body incidence. It serializes typed rows and uses `SemanticImports::empty()` exactly as the existing isolated runner does.

No generated Lean trace was written. Run 2 compiled, started the adapter, then failed before writing because `OUTPUT` is repository-relative and Cargo was invoked with the package directory as the working directory. The trace path does not exist at either the repository target or the accidental package-relative location. The no-retry limit is exhausted; no trace or successful emission is claimed.

The owner equation remains open. The runner's lowerer receives `SemanticImports::empty()` and does not receive an `OriginalSource.Context` or root scope snapshot. HIR authenticates the declaration `HirBinding`/`DefId`/`DefinitionRootId`, the exact CST definition key, local source occurrences and parameter-resolution identities, but exposes no mapping from those owners to `OriginalSource.Declaration`, the caller's `Context`, or its ambient `ScopeEntry` list. The downstream inference API also has no such Context parameter. Consequently no actual root Context, source-owner telescope, or `Identity` can be populated from this runner. `None` for `CallerContextOrigin` is unobserved caller preparation, not evidence of an empty context. The actual full-root `sourceOwners` telescope requires the missing root Context/route/ambient source equation.

## Cargo receipts

Both runs used `cargo run --locked --offline --bin original_owner_reify`, one build job, a 120-second timeout/CPU limit, 1 GiB address-space limit, and the isolated target `/tmp/yulang-source-owner-reification-20261027/impl/target`.

1. Run 1, package cwd, exit 101. The initial source failed compilation on two adapter errors: `SourceIdentityError` does not implement `std::error::Error` for `?`, and `source_position` returned `PositionId` but was followed by an extra `?`. Log: `/tmp/yulang-source-owner-reification-20261027/impl/cargo-run-1.log`; SHA-256 `dff6ac218271f02b514bb66311c589068e24a9ad1d3bc1e0392a135d56ae96d9`.
2. Run 2, package cwd, exit 1. The corrected source compiled successfully; runtime failed with `Os { code: 2, kind: NotFound, message: "No such file or directory" }` while writing the repository-relative output path from package cwd. Log: `/tmp/yulang-source-owner-reification-20261027/impl/cargo-run-2.log`; SHA-256 `fad22bba33021357a49d0bc2273c1fd6d3b2e2eeb01f882dddf0810d22429507`.

No additional Cargo run or compiled-binary invocation was performed. No tests were run. The output path `notes/theory/lean/YulangClosure/OriginalSourceOwnerReificationTrace.lean` is absent and has no hash.

## Remaining status

- Source code: compiled by Cargo run 2, not independently reviewed.
- Generated trace and Lean correspondence consumer: NOT PRODUCED / NOT CHECKED.
- Original-source Declaration / root Context / ambient scope / event telescope correspondence: OPEN at the owner equation above.
- Full inference/executor parent goal and all production gates: OPEN.
- Requested model/effort: registered Luna/high implementer; observed model, effort, worker session UUID: UNKNOWN.
- Worker stop: no process remains active; Cargo run 2 exited and no binary is running.
- Disposable scratch: `/tmp/yulang-source-owner-reification-20261027/impl/target/` plus the two preserved Cargo logs above.
