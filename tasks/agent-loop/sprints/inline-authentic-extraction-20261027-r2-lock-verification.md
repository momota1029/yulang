# INLINE-AUTHENTIC-EXTRACTION-20261027/r2 — independent lock/graph verification

Disposition: **PASS for the isolated dependency graph only.** This primary
verification authorizes preparing a new execution contract revision; it does
not authorize compilation, prove source extraction, or close a Lean parent.

## Inputs checked

- Frozen original r2 contract: SHA-256
  `af6c0f6e462f6ad414f7c82572216422925fe9ff3a68c1fe8d99df8f1605672e`.
- Frozen r2 revision 2 lock-reconciliation contract: SHA-256
  `710fb4436e87ecd8575c6f01b9cd0109e098939275c3f0c4b9c5445b7db9fe9c`.
- Stage-1 outcome receipt: SHA-256
  `e12c60217b8a5c4baf9e0cf78074234b4a1449ccad7fabcf2bbbfeb15ea2e13b`.
- Implementation handoff revision 1 was acknowledged at SHA-256
  `4506d65a3e01d571c648c22150ee40294d2798056befdb93ea76c905290f2b31`;
  sequential revision 2 is SHA-256
  `6bbf5be439a268d63d38d990b5f073ce8021c6e5e0892610bd286b4028279031`.
- Pinned root `Cargo.lock`: SHA-256
  `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`.
- Isolated `Cargo.toml`: SHA-256
  `21c64b4a22318a1ae89c346357161812a6ac313b6f0c4999853272cf73e2832b`.
- Isolated corrected `Cargo.lock`: SHA-256
  `2ee467b8f6416aa7dda36f96e3401a0b0ae24a739ff7c6a2efccc1323777ee91`.
- Full `cargo metadata` stdout/graph:
  `/tmp/yulang-inline-authentic-extraction-20261027-r2/impl/resolved-graph-r2.stdout.json`,
  SHA-256 `595365e8f394504fcc5c04e638107158351e3731284877b5bb12044358778fb1`.
- Exact command text SHA-256
  `c6e8497a8ca8c6ba0de165562eff21de030011bd5b0f84f42883411aa260eb61`;
  stderr is empty (SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`);
  exit/duration receipt SHA-256
  `23e0255be75b5397b94714ce534e16fe22bf929da7bb97ccda618ef476b1295e` reports
  exit 0 and 0.05 seconds.

## Independent comparison

I parsed the pinned root and isolated lockfiles as TOML and the two metadata
outputs as JSON; no Cargo, build, test, Lean or Lake process was run for this
comparison. The lock diff contains only the intended package record changes:
`rowan` 0.15.19→0.15.17 and `unicode-ident` 1.0.27→1.0.24, including the root
rowan dependency qualifier `hashbrown 0.14.5`. The manifest and all dependency
edges are unchanged.

All **22/22** isolated registry `(name, version, checksum)` tuples are present
identically in the pinned root lock. The metadata graph has 26 package records,
26 resolve nodes and exactly one isolated workspace member. Package-name and
dependency-edge sets are unchanged from stage 1. `yu-solver` occurs in no
package, node or edge. The query succeeded under `--offline --locked`, so Cargo
reported no required lock update or unavailable package.

No source extraction, HIR owner authentication, Lean proposition or theorem was
executed or verified here. Full original A/B, soundness, effect hygiene,
principality, termination, source/native correspondence and production remain
OPEN. This receipt authorizes only a new immutable contract revision that pins
these exact graph and lock hashes before extractor code or compilation.
