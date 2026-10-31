# R94 admission — exact-input check for R93

Sprint: `EFFECT-PERMISSION-LOGICAL-OCCURRENCES/20261101-R94`.
Baseline: `yulang3` at `120db95f8f4ad9505ae245884f3c3ab7e8d18c71`, equal to
`origin/yulang3` when admitted.

The continuing user-authorized Yulang Rust/Lean soundness objective covers this
bounded verification continuation. The dispatcher selected independent exact
input review followed by one check of the unchanged R93 Lean candidate. The
source occurrence theorem and its original parent quantifiers remain unchanged.

Frozen contract revision 1 SHA-256:
`b00a4ddf0aec31ed0a5253b29afa2d7c980b48f1948139fb760f5cab55d19cde`.
Frozen input manifest SHA-256:
`e8a15ae3e3f749101cbb38631b7776dd8a36db0c68c59712158db34fe97bc370`.
The exact in-memory input is 106,897 bytes, SHA-256
`8bd62910afba8530f2140bd5b0db0d5fb5281c4651b87a88f78c51dc53d0d7`.
The three component files and all predecessor evidence are pinned by the
manifest. No separator bytes are inserted; only the two inter-module imports
are removed, while `import Std` is retained.

The exact review lease is
`tasks/agent-loop/inbox/effect-permission-logical-occurrences-r94-input-review.md`.
The exact primary verification/authorization lease is
`tasks/agent-loop/inbox/effect-permission-logical-occurrences-r94-verification.md`.
The exact independent result-review lease is
`tasks/agent-loop/inbox/effect-permission-logical-occurrences-r94-result-review.md`.
The reviewer is admitted as a fresh `compiler_referee` for at most 300 seconds;
no runtime identity or launch is claimed by this admission receipt. Primary
execution is at most 300 seconds including one 120-second Lean invocation.
Result review is at most 200 seconds. Total: 800 seconds; Astra: 0.

No Lean/Lake/build/test call is authorized yet. The one Lean call is authorized
only after the independent input-review handoff passes exact byte/hash, import,
query-count and context checks, and after Luna pushes a separate exact-input
execution authorization. The candidate and all dependencies remain frozen.
No Rust or source-policy edit, cache, environment, worktree, project copy or
scratch is authorized.

R93 stays closed as a statically reviewed unchecked candidate with zero calls.
Its uncertain reviewer time is neither reused nor reset. Source-owned semantic
admission/readout, the original A/B claims, source/native correspondence,
principality, termination and production remain OPEN.
