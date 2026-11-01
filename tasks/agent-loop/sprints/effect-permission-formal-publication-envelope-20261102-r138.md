# R138 — trace failed formal-permission publication to the session boundary

Status: admitted read-only source audit. Parent gates remain OPEN.
Original goal: Yulang inference soundness and effect hygiene; no semantic/domain narrowing.
Baseline: `4c1d58a646a1101c080659ebfed6ae7862d8aded` (= `origin/yulang3`).
Inputs: R137 outcome SHA-256 `82fd775010eb1b865928510bed1d34d282c0d46768f6ee93054ca0d670748231`; R137 source SHA-256 `0a81bca2f61c6f8665a7c90374e2872f3a135d1c06827c4fd493f629c8180a51`; review SHA-256 `f178ab6e42afa9fa84568ada3f373bc41c156528a9646c90764ae67ef857da3d`.

## Fixed outcome

For every production caller of `FormalAnnotation` and the relevant outer
`FormalEntry`, establish one of: (a) post-publication failure restores all
published permissions/domains before any successful result; or (b) that failed
session terminates/is discarded and cannot feed a later successful solve or
permission consumer. Trace from constructors through error propagation,
rollback journal and final session ownership/reuse. If neither holds, report
the first exact production path where failed published state remains reachable
by successful output or a consumer. A local constructor `Err` alone is not a
counterexample.

## Source assignment

One Luna/high implementer, 600 seconds, read-only. Sole output lease:
`tasks/agent-loop/inbox/effect-permission-formal-publication-envelope-r138-source.md`.
Inspect only immutable committed baseline source. Relevant owners include
`candidate_effect.rs`, `candidate_source.rs`, `lib.rs`, and the exact route,
transaction, finalization, consumer or session-owner files reached by the call
graph. Reuse R123/R124 lifecycle evidence only if exact hashes and scope match.
Do not inspect dirty diffs, quarantined runtime paths or untracked foreign
artifacts. No Rust edits, build/tests, Lean, scratch or Git mutation.

Fresh independent compiler-referee review: 240 seconds after source handoff
freezes; exact output `tasks/agent-loop/history/effect-permission-formal-publication-envelope-r138-review.md`.

## Falsifier, resources, and limits

Falsifier: a supported production route returns failure after publication,
retains/reuses that same session, and reaches a successful output or consumer
without restoring or excluding the failed attempt. Conversely, do not claim
discard unless the exact owner proves that state cannot be reused. Tests and
test-only transaction wrappers do not discharge the production path.

Total envelope 1,080 seconds; Astra, compiler, tests, Lean, new environments
and storage probes: zero. No source permission is granted. The R137 identity
encoding and native inventory equality remain OPEN; do not invent Lean ID
encodings or move correspondence into unmarked assumptions. Only Luna owns
central state and Git.
