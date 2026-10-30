# R36 stage ledger — source-owned callback use

Sprint: `EFFECT-PERMISSION-SOURCE-USE/20261031-R36`
Contract SHA-256: `c471c7dd5d8ef2515022f4665f1ef2151577141a3f0942ea107489ecd86c5ac0`
Input manifest SHA-256: `cf03b01ba1cb057972303540dd7deb881e0cfff2f8dbafd93e4912035bee37e4`
Admission SHA-256: `c28d9b493d7a6e00bfd9d4f99ac46990e1bf246a70bd3ace9225021afa36e92d`.

| Stage | State | Evidence / boundary |
| --- | --- | --- |
| Contract and dependencies | ADMITTED | R36 contract and 15-file manifest pinned at baseline `1388bdc476e5dc0c0bb96532715c7280aa95b10e`. |
| Rust construction | NOT_STARTED | Exact leases: `program.rs` and Rust handoff. No consumer-file access. |
| Lean construction and audit | NOT_STARTED | Exact leases: `SourceCallbackUseR36.lean` and proof handoff; pinned Lean 4.35.0 stdin audit. |
| Independent review | NOT_STARTED | Wait for both producer freezes; reviewer may write only review handoff. |
| Luna integration and Git | NOT_STARTED | Exact-path staging only after review passes. |

No builds/tests or new environments are permitted. Preserve symbolic rows, annotation polarity, all pending questions, unknown workers and quarantined paths. Runtime execution, Grant/Catch, Rust-Lean simulation, original A/B and whole-language claims remain OPEN.
