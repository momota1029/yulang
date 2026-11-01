# R139 outcome — identity table candidate not accepted

Sprint: `EFFECT-PERMISSION-ID-ENCODING/20261102-R139`
Baseline: `4c1d58a646a1101c080659ebfed6ae7862d8aded`
Contract v1 SHA-256: `717acc2e9c3bd70f19a0b74854802952ab0eea6ccf62fab104c5075997ee4afb`
Independent review: `tasks/agent-loop/history/effect-permission-id-encoding-20261102-r139-review.md`, SHA-256 `f40a05d3c791cdf4d10c98f283938e9347a5f1dbc68e6943d70a956c86d6b508`.

## Outcome

The test-only Rust candidate uses one snapshot-local `HashMap<TaggedKey, u32>` table for source and retained-native encoding. The registered Rust key types support the candidate's `Clone`/`Eq`/`Hash` use, tag variants remain distinct, duplicate concrete members retain order and multiplicity, and explicit reservation/code-width errors propagate before the snapshot return. The reviewer found no blocking issue in those bounded structural claims.

The source handoff is **not accepted as a source/native correspondence result**. It overstates `SourceNodeKey` injectivity: the pinned zero-width sibling fixture has equal keys. The fixture is not a demonstrated supported-source counterexample; accepted-source uniqueness remains OPEN. The handoff also overstates allocation failure coverage because some vectors and cloned boxed symbols can allocate infallibly. The R138 digest in the v1 contract and source handoff is stale; the correct outcome SHA-256 is `2cfe94f5dd822c4df4619fa194186c2537393c1c3ed8340e244f56b6e93ac480`.

## Proof and remaining gates

The Lean candidate has 19 table-local declarations, but its one permitted check and version queries exited `-6` before elaboration with `failed to create thread: Resource temporarily unavailable`. Types and complete axiom audits were not obtained. Keep the module **CONSTRUCTED_BUT_UNCHECKED**; do not retry under R139.

The table candidate accepts arbitrary source annotations independently from a `State`; it does not bind source rows to the exact successful constructor call or establish the filtered native traversal order. Lean's seven tags also omit Rust's `FormalPosition` tag. The original `SourceProblem.InferenceSoundness`, effect-hygiene H, A/B, source/native inventory equality, consumer correspondence, and production remain OPEN.

## Next evidence

R140 supersedes the rejected mapping attempt by tracing a single real constructor invocation and its successful appended permission interval. Its source/native order, row filtering, polarity, path and root-entry separation are explicit falsifiers. R139 v1 artifacts remain preserved and are not silently revised.

No Rust source was changed; no build, test or further Lean check ran. No source artifact is integrated. The bounded outcome is research-only.
