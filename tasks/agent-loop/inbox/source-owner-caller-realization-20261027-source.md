# Source-owner caller realization: source-lane handoff

Status: **STOPPED after Cargo call 2/2 runtime failure**. No Lean trace was
generated or published. No tests, Lean, Lake, further Cargo, or binary rerun
was performed.

## Frozen implementation attempt

- Leased adapter: `tools/inline-authentic-extraction/src/bin/original_caller_reify.rs`
- Call-1 adapter SHA-256: `3cbf6b2da27938006e530bd41389b63d8a5ca5e32c004f4055e18258edca5e98`
- Frozen schema: `notes/theory/lean/YulangClosure/OriginalSourceCallerSchema.lean`
- Schema SHA-256: `9bb15c7f383a997c4e7d63efd521704c925e62c95072f81ad18ad2aec9ba30b9`
- Intended trace target (not created):
  `notes/theory/lean/YulangClosure/OriginalSourceCallerReificationTrace.lean`
- The selected nested-shadow input keeps the accepted subtree and outer
  parameter argument unchanged. Alias and glob lookups are represented as
  separate names, joined to the provider declaration through exact
  `SourceExportId` equality and a shared canonical export ordinal.

## Runtime receipt

- Baseline: `90d6332ffc30fdb9f005e1f788bfdb3eaf82bc8c`
- Call-1 contract SHA-256
  `a46515f07875e39a4e1b6f96647228d6968b1183f0183fd2d86c69073455c56d`,
  admitted at `82eec85b6`.
- Command: `taskset -c 0 prlimit --as=1073741824 --cpu=120 -- timeout 120s bash /tmp/yulang-source-owner-caller-realization-20261027/impl/run1.sh`
- Cargo argv: `cargo run --locked --offline --manifest-path tools/inline-authentic-extraction/Cargo.toml --bin original_caller_reify -- /home/momota1029/rust/yulang/notes/theory/lean/YulangClosure/OriginalSourceCallerReificationTrace.lean`
- CWD: `/home/momota1029/rust/yulang`
- UTC: `2026-10-27T12:17:56Z` to `2026-10-27T12:18:20Z`
- Wrapper/exec status: `101`; Cargo child status: `101`; timeout did not fire.
- Receipt: `/tmp/yulang-source-owner-caller-realization-20261027/impl/cargo-call-1.receipt.txt`
- Receipt wrapper SHA-256:
  `0ce1f3a621f877908ec7553b6468ff22260911f38727ee16d439ef0d3725c36c`
- Captured stderr SHA-256:
  `d1910194dd404fd6bcef6b26e841ea7a916471daeaae3308858f91c8cd59dc8e`
- Captured stdout SHA-256:
  `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
- Full environment bytes and stdout/stderr are preserved under the scratch
  directory above. These call-1 artifacts remain immutable through the bounded
  continuation.

## Exact compile blockers

1. Seven `?` conversions failed because `HirAvailabilityError` does not
   implement `std::error::Error`: consumer/provider `index_source_exports`,
   direct and provider `definition_source_key`, and consumer/provider/foreign
   `SemanticImports::with_source_imports`.
2. `SyntaxKind::UseStatement` does not exist; the root inventory check needs
   the actual `SyntaxKind::UseDeclaration`.

## Luna-authorized single retry amendment

Luna's continuation is committed at `731fd3368179e18c4d207e9ac45d16f85937efc7`;
the amended contract SHA-256 is
`9c6bb17280250a83c68f42cc17dc32ccc331e60a7f5290af1d942b5e139432e6`.
It explicitly overrides the earlier stop-at-first-failure instruction for
exactly one final Cargo call. The only adapter changes were the seven
`HirAvailabilityError` conversions routed through the existing
`availability(...)` helper and `UseStatement` changed to `UseDeclaration`.
No corpus, schema, owner join, selected subtree, or rejection order changed.

The original call-1 receipt, command, environment, stdout/stderr, exit statuses
and diagnostic bytes listed above remain immutable in scratch. Rehashing the
amended adapter and contract plus the unchanged inherited pin sets found zero
mismatches across 56 governing/import-configuration pins and 10 exact
source-map pins. The contract's direct artifacts also matched: prior adapter,
schema and owner artifacts, module owner files, Cargo manifest/lock, and prior
review handoff. The amended adapter hash before final Cargo authorization is
`4652e48fe3305d34c9d271f3a711cee97785a1d167ca19d4a4b01c147e775620`.

This amendment permits one final `--locked --offline` Cargo invocation only,
with explicit `taskset -c 0`, `prlimit --as=1073741824 --cpu=120`, and
`timeout 120s`, plus full in-envelope environment and wrapper/child status
receipts. No compile-only call, tests, binary rerun, Lean/Lake, or further
retry is authorized. After that call, freeze and stop regardless of outcome.

## Final Cargo call 2 receipt and obstruction

- Exact command:
  `taskset -c 0 prlimit --as=1073741824 --cpu=120 -- timeout 120s bash /tmp/yulang-source-owner-caller-realization-20261027/impl/run2.sh`
- Exact Cargo argv:
  `cargo run --locked --offline --manifest-path tools/inline-authentic-extraction/Cargo.toml --bin original_caller_reify -- /home/momota1029/rust/yulang/notes/theory/lean/YulangClosure/OriginalSourceCallerReificationTrace.lean`
- CWD: `/home/momota1029/rust/yulang`; selected and observed affinity: CPU 0.
- Inherited limits receipt SHA-256:
  `751928415512903447ed94a38c33a49ba17062a0feb16c81062a8cb8b75b0708`; explicit
  limits remained 1 GiB address space, 120 CPU seconds, 120-second wall timeout.
- UTC: `2026-10-27T12:23:48Z` to `2026-10-27T12:23:49Z`; wall time 0.964s.
- Cargo compiled the adapter successfully, then the program panicked before
  output publication at `original_caller_reify.rs:110:68`:
  `provider parse artifact: MalformedSource`.
- Cargo child status: `101`; in-envelope wrapper status: `101`; timeout did not
  fire. No trace output file was created.
- Receipt:
  `/tmp/yulang-source-owner-caller-realization-20261027/impl/cargo-call-2.receipt.txt`,
  SHA-256 `0ccd23419fffeebdf042b28115e63fb486ba07006bae72ac4b2b50b7a84852fb`.
- Wrapper script SHA-256:
  `343b07868e5c4bccb5ceb33996bc70f1ee1dead193523d08fc277e566aa6115d`.
- Full environment SHA-256:
  `f951ab12d707aa45df9e3b430653cd8c694d64547ed09697c51a50a6b9e4d001`.
- Stdout SHA-256:
  `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- Stderr SHA-256:
  `6827762152eb75e8ccec9b579240736fa867348097c42a4574b14f2c881a8ed5`.
- The produced Cargo build directory is
  `tools/inline-authentic-extraction/target/`; it is known disposable build
  output for primary-only workspace hygiene. It was not removed or modified
  after the bounded call.

No retry remains. The exact import-to-`OriginalSource.Context` interpretation
and module-import-root-to-`OriginalSource.Source`/root equation remain OPEN;
the runtime obstruction supplies no semantic conclusion.

## Exact next source/proof obligations

- The adapter repair is present; the final Cargo call is still pending Luna's
  exact pre-call acknowledgement.
- Produce owner-checked rows for consumer and provider parse roots, complete
  ordered root inventory, raw alias/glob import leaves, provider exports,
  exact resolver routes, and imported LocalSource occurrences.
- Preserve the existing selected `OriginTable` and nested-shadow equations;
  do not infer imported `Binding` fields from a resolver identity.
- Proof lane must establish finite-table consistency for exact provider joins
  and the selected unchanged instance after a generated trace exists.
- Still missing: an adopted equation from resolved import identity to every
  `OriginalSource.Binding` field in `Context`; an adopted equation from module
  import roots to original `Source`/root rules (including route and ambient
  scope); runtime `OwnedFrame` provenance. No complete original `RuleTree` or
  `Context` is claimed by this handoff.
