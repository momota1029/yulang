# R95 admission — corrected exact-input verification

Sprint: `EFFECT-PERMISSION-LOGICAL-OCCURRENCES/20261101-R95`.
Baseline: `yulang3` at `9a80a223ebb8b82eaf49fecc9454c5acfe1a636d`, equal to
`origin/yulang3` at admission.

The continuing user-authorized Yulang Rust/Lean soundness objective covers this
bounded correction and verification. The dispatcher recommended preserving
R94's blocking result and correcting only the new R95 authority records. The
R93 candidate, source dependencies, theorem queries and parent quantifiers
remain unchanged.

Contract revision 1 SHA-256:
`787d97362f3ca2d7a6a8e742009408513b0ca73a729228ec430db334727e7a1f`.
Input manifest SHA-256:
`0cc19b0cc76cd5b9a456d62bb3a7d48d656698afefd22c1bc3eccfbd4ed4142c`.
The exact stdin is 106,897 bytes and SHA-256
`8bd62910afba8530f2140bd5b150db0d5fb5281c4651b87a88f78c51dc53d0d7` (64
hexadecimal characters). Its components and the pinned Lean 4.35.0 executable
are recorded in the manifest.

Exact leases:

- Input review: `tasks/agent-loop/inbox/effect-permission-logical-occurrences-r95-input-review.md`
- Primary authorization and execution receipt: `tasks/agent-loop/inbox/effect-permission-logical-occurrences-r95-verification.md`
- Independent result review: `tasks/agent-loop/inbox/effect-permission-logical-occurrences-r95-result-review.md`

The input reviewer is admitted for at most 60 seconds. Primary execution is at
most 180 seconds including one Lean call capped at 120 seconds. Result review
is at most 120 seconds. Total 360 seconds; Astra 0. R94's separately charged
32 seconds and R93's unknown reviewer time are not reused.

No Lean/Lake/build/test call is authorized yet. Execution is authorized only
after an independent reviewer confirms the corrected exact digest, input
reconstruction and ten query pairs, followed by a separate pushed primary
authorization. No repair, Rust edit, source-policy change, or semantic change
is authorized. No environment, worktree, project copy, cache or scratch may be
created.

R94 remains closed with zero Lean calls. The source occurrence candidate
remains unchecked until R95 execution and result review succeed. Original A/B,
semantic admission/readout, source/native correspondence, effect hygiene,
principality, termination and production remain OPEN.
