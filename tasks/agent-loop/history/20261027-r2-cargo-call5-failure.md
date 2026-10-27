# R2 Cargo call 5 failure receipt

Sprint: `INLINE-AUTHENTIC-EXTRACTION-20261027/r2`, contract rev4
(`tasks/agent-loop/sprints/inline-authentic-extraction-20261027-r2-rev4.md`,
SHA-256 `1e99d83d65fd89705a4ce28db5da111b3d1e0fa4055faba1513b7bb8ec65ba0f`).

## Frozen inputs and process receipts

- Extractor source: `tools/inline-authentic-extraction/src/main.rs`,
  SHA-256 `9c484bf76e5c4d57ac616f1e8864e6bcd6fe388164f45eb3a1bc3db2ad02fa87`.
- Manifest SHA-256 `21c64b4a22318a1ae89c346357161812a6ac313b6f0c4999853272cf73e2832b`;
  lock SHA-256 `2ee467b8f6416aa7dda36f96f3401a0b0ae24a739ff7c6a2efccc1323777ee91`.
- Command `/tmp/yulang-inline-authentic-extraction-20261027-r2/impl/run-r4.command.txt`,
  SHA-256 `16ca8fc067fbe79a839ceedae10b88fa30c4fb6e8c9624eecb4b98d064673a52`.
- Environment receipt `run-r4.environment.txt`, SHA-256
  `98df7c1b1a8a93a4b02e3f5d605502619b6c543a4b464ce71b04055024f31d14`.
- Stdout `run-r4.stdout`, SHA-256
  `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- Stderr `run-r4.stderr`, SHA-256
  `9bb08dbea83a81df6f5938d357b340416362522cf1a75447b564f0e2e5f908e8`.
- Exit/time receipt `run-r4.time`, SHA-256
  `e222648df9e81a68967d6597fae93d12bd1b620bfff166cf9f624f440bbb31bc`;
  exit 101 after 17.57 seconds.

## Outcome

Cargo call 5/6 compiled the isolated dependencies, then failed compiling the
extractor before `main` ran. There are ten Rust errors: three calls to
`PositionId::ordinal()` (no such method) and seven `?` conversions from
`HirAvailabilityError` (which does not implement `std::error::Error`). No trace
was produced. The worker reports that Cargo/rustc processes ended; `target-r4`
is retained under the leased scratch root. These are compile defects in the
provisional extractor, not a source-language counterexample. Call 6 remains
unused and requires a new immutable revision. All parent gates remain OPEN.
