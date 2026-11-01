# R111 source-only integration policy revision

## User authorization

The user explicitly requested: “Rust実装も適当に解析してpushまでしてほしい……” (“Please analyze the Rust implementation too and take it through to push”). This is treated as a direct, versioned revision to R111's prior no-source-integration gate for the exact already-reviewed three-file candidate below.

## Narrow authorization

This revision authorizes source-only integration and a normal push of the exact R111 candidate, without Cargo/compiler verification. It applies only to these reconstructed complete-file hashes:

| Path | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `6eb6b5df29bda1d1bd1fecabcbc2cc6e85e777dda2045f1d1ab86084f64cd84f` |
| `crates/yu-solver/src/candidate_receiver.rs` | `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf` |
| `crates/yu-solver/src/candidate_effect.rs` | `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01` |

The exact patch is the immutable R111 handoff, revision 3, SHA-256
`54a79a1b4f49d75b78bd3c3e96ff2c317941c57e24dfbad6e2c441309f131d9d`.
Primary independently reconstructed all seven replacements in memory from the
current HEAD blobs; each old pattern occurred exactly once and the resulting
complete-file hashes matched the three authorized targets.

## Evidence boundary

R111's fresh independent compiler-referee review passed the exact source
reconstruction and Member ownership analysis. Compilation was explicitly
blocked by the unavailable private aggregate 6-GiB cap and absent remote
verifier. No Cargo/compiler/build/test invocation has been made. The source
commit and push therefore record the user's requested uncompiled candidate;
they do not claim that it compiles, passes tests, establishes source/native
correspondence, closes the original A/B claims, or is production-ready.

This authorization does not apply to any other dirty working-tree content,
the R131 in-memory adapter candidate, quarantined runtime files, or subsequent
source changes. Those require their own exact review and authority.
