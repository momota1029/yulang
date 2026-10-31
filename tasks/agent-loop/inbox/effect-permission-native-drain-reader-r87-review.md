# R87 pre-execution review — primary transcription of independent verdict

Reviewer: `/root/r86_repair_review` (`compiler_referee`), independent and
read-only. The reviewer returned the verdict and evidence in a message because
the registered role cannot write files. This file transcribes that frozen
message; it is not a self-review. No execution was authorized by this review.

## Verdict

**PASS for pre-execution readiness.** No blocking, major, or minor findings
within the declared finite, conditional scope. This does not accept unchecked
theorems or authorize a Lean call.

## Frozen artifacts verified

| Artifact | SHA-256 |
| --- | --- |
| Contract | `2ec7f33760b4ef8cdb3ac434dcf415f473a2019f4acf87c25786f77e0fc81261` |
| Corrected manifest | `e3d1b0590ea1fb179cc89039665b04d0d4d9bd2ec6a63290df4f90011fe2be96` |
| Candidate, 28,950 bytes | `5439e697535c6d3f153db7f75e3b2a58c7b6755e41a93420c479b7a36a0c6d23` |
| Proof handoff | `fadc5a3be55e7237f91cb0d3dfffd40dc7d6c750e7ad7c56ae92b1be51b60190` |
| Source report | `3e911c32e76931cf8ff38d0a97de2a8eb711c3a3aac5e45e7bf7cd2951fae3d8` |

Both pinned Rust inputs match the manifest: `candidate_context.rs`, 265,778
bytes, SHA-256 `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`;
`candidate_receiver.rs`, 292,001 bytes, SHA-256
`6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2`.

The reviewer independently reconstructed the proposed input as 150,997 bytes,
SHA-256 `e277bb3673cde7f44ee4bc4aa9e1145de2c6e15187a72d34091a1878e0862358`.
The 35 complete type/axiom query pairs are 6,204 bytes, SHA-256
`48030ee348c82ab1787b25f1f20679def5cab1076982ac4d565e907f4126c8f0`.
Earlier R84/R85 queries remain included. No failed R86 declaration is imported
or flattened. The primary independently reconstructed the exact R84 and R85
accepted prefixes and the R87 input in memory and obtained the same byte counts
and hashes.

## Semantic findings and open premises

All 35 theorem statements, definitions, and proof structures were inspected.
The plain-data combinators avoid R86's dependent-selector reduction pattern;
certificates are constructed only after each reader's own correspondence
theorem. The four reader boundaries remain distinct:

- Uncut publication leaves the attached bit, incoming relation, and replay
  acknowledgement unrestricted.
- Cut-window publication requires pending attachment and cut-local uniqueness.
- Internal selection uses global inventory selection and requires completed
  attachment, with missing and ambiguous branches preserved.
- The saved relation covers the receipt factor. It does not import the
  construction-inherited incoming/replay/global-uniqueness checks, and does not
  establish the other saved-reader prelude or pointer-token authenticity.

The proposed pending-plus-completion carrier changes arbitrary-state reader
acceptance; it is not substituted for a current reader or treated as an
established seal. The unchanged R84 Root blocker remains explicit.

Open obligations include native extraction and reference-token authenticity;
the same-snapshot equation for omitted saved prelude/route/formal/emission
checks; full occurrence versus HIR projection correspondence; cut-local,
global, R84 route, and R57 relation-ID selector bridges; authentication of the
R57 projection maps; whole-crate transition coverage; standalone imports;
original A/B; and production.

Falsifiers include missing or malformed matching Origins, duplicate Origins or
completions, equal-valued duplicate records, invalid cuts, competitors outside
publication cuts, completed attachments accepted by uncut but rejected by cut,
and forged equal-reference tokens with different payloads. The last case stays
outside authenticated native correspondence.

## Gate

The exact input recipe is ready for a separate committed-and-pushed
authorization. The 35 proofs, their transitive axioms, native correspondence,
original A/B, and production remain unchecked or open until execution and an
independent result audit. Any error, recovered `sorryAx`, unexpected axiom,
hash drift, or falsifier blocks acceptance.

Reviewer operations: no file writes, Lean, build, test, Git, cache, target,
scratch, environment, or worktree. Reviewer verdict was returned at the
independent role boundary; Luna retains authorization, execution, state, and
Git ownership.
