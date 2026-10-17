# NPAIR source-admission final verification

Sprint: `npair-source-admission-correspondence-20261018`, same parent
`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`. Original source domain and
quantifiers are unchanged. Original-condition closure remains **0**.

## Frozen implementation and test evidence

- Code/test: `crates/yu-solver/src/candidate_source.rs`, SHA-256
  `74a83e04a3ecc88a8711ae9ffb2d2bc7274f40eaa2f7eb789ebb0c0980354067`.
- Contract: `notes/design/2026-10-18-npair-source-admission-contract.md`, SHA-256
  `692aa39ec37f522e921634134551dad1933b736e5afd2eff463213970a0fb609`.
- HIR first-failure analysis: `notes/theory/2026-10-18-npair-hir-first-failure.md`,
  SHA-256 `dd964fc6ed2c87ab2eb3d33ae583d1731d009ce6da58eee2d7b7fb2dee530542`.
- Integrated continuation: `notes/progress/2026-10-18-npair-source-admission-integrated-continuation.md`,
  SHA-256 `42d5e51e0638fbb129ea7037a1cfb27c312aec95064f212a01beeab36202a045`.

The final focused command was:

```sh
cargo test -p yu-solver --features shadow-apply-candidate \
  candidate_source::formal_concrete_negative_source_tests::source_entry_admits_only_nonempty_concrete_negative_formal_rows \
  -- --exact --nocapture
```

Result: **1 passed, 0 failed**. The target nonempty concrete-only negative
formal-port row passed ordinary parse, HIR lowering, source annotation/identity
checks and `CandidateInference::solve`. Formerly admitted omitted/singleton
symbolic and positive-concrete cases stayed accepted. Empty and mixed rows
were refused after reaching the solver. A multiple-symbol row was refused at
HIR with `StructuralProjection`, before solver entry; the test checks this
specific earlier boundary and does not attribute it to solver preflight.

Earlier attempts are retained in
`notes/progress/2026-10-18-npair-source-admission-second-hir-failure.md` and
`notes/progress/2026-10-18-npair-source-admission-integrated-continuation.md`.
One earlier compile failure was only a test diagnostic using a nonexistent
`ParsedFile::syntax()` method and did not execute a test. The final test is the
only successful runtime receipt in this continuation.

## Claim and remaining work

The result establishes one reviewed-scope normal source path and adjacent
source refusals. It does not establish the universal source-to-native
correspondence, any original F1/FK1/N-Transport/Call obligation, or
soundness/principality/termination. The HIR audit establishes that
`StructuralProjection` also hides `FormationError::Unsupported`; the precise
producer of the earlier failed fixtures remains unknown. No HIR or syntax code
was changed.

The candidate is frozen for fresh independent compiler and spec review. It is
not integrated or committed pending those reviews and Luna adjudication.
