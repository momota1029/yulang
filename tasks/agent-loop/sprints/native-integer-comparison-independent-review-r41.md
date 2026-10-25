# Sprint NATIVE-INTEGER-COMPARISON-INDEPENDENT-REVIEW-20261026/r41

Status: READY; Luna primary, one fresh independent spec auditor.
Branch: `research/simple-sub-intrusion`
Baseline: `9c104326a8ee688ec98a1f26bb5f700ad3fa85ca`

## Fixed outcome

Independently review the frozen R40/r8 Lean candidate and its recorded final audit for exact theorem/scope and Rust-to-model correspondence. This packet supplies source/math review only. It does not rerun Lean, checker, builds or tests; does not alter the candidate; and does not retroactively change R40's FAILED status caused by its 14-call overrun. A clean review is evidence for Luna's later acceptance/integration decision, not a production or whole-executor theorem.

## Frozen inputs

- R40 contract `tasks/agent-loop/sprints/native-integer-comparison-order-r40.md`: `c67b3f0a916bfc47a3bd01ce2ce7d406595e4011ab8a3248e732a03d8cd4dec9`.
- Candidate `notes/theory/lean/YulangClosure/NativeIntegerComparison.lean`: `2352602b7047611e9f9722d788ed1acdf9f4960d178c48f6a08b1a7054f93e79`.
- Worker handoff `tasks/agent-loop/inbox/native-integer-comparison-r40.md`: `e293493a396f834a147dfb16c206e56ddb0aa7fd938ede016f65adc9b693b7d3`.
- Primary verification receipt `tasks/agent-loop/inbox/native-integer-comparison-r40-primary-verification.txt`: `bbd43b91179fa278f248d29bb693b7bb314222d1966ad9d85380b4a79dccf050`.
- Exact primary audit source `notes/theory/lean/.lake/native-integer-comparison-r40-audit.lean`: `2ab35bb0b8c428e4e016a910fbcb0fc2cf456001e32f1f022841b8a91e2506ac`.
- Manuscript `docs/yulang-operational-type-safety-ja.tex`: `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
- Readback `notes/theory/lean/YulangClosure/NativeLiteralReadback.lean`: `53a745397fed4b319225541b8e764a32cdc72032ca4e8be48d9d4a23d3901c54`.
- Runtime `tools/inference-playground/src/runtime/decimal.rs`: `83ba443036c7da05f9d72d4bbba98b05c4cab2135062743ffe8e3f05250d1cae`; consumers `machine.rs`: `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e`; HIR mapping `source_annotation.rs`: `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f`.
- Producer invariant `notes/theory/2026-10-25-native-literal-producer-invariant.md`: `1f73d0a4e221cb2d2a182876cf9928ebd3cab34edd6d36f4a46bb6bd3ca9a651`.

## Review questions

1. Do the unchanged Lean declarations preserve the original successful `decodeInteger` hypotheses and establish parser success/rejection, signed-decimal ordering and all five Boolean consumer results without narrowing the grammar or replacing the decimal algorithm with direct mathematical-integer comparison?
2. Do the model branches correspond to the pinned Rust `parts`/`compare` implementation, including optional minus, ASCII digit rejection, leading-zero and negative-zero normalization, length then lexicographic magnitude ordering, negative reversal, mixed signs, malformed operands and unbounded decimal values?
3. Do the exact HIR identities and `machine.rs` branches map `int_eq`, `int_lt`, `int_le`, `int_gt`, `int_ge` to the audited Boolean projections, and does the manuscript supply the claimed mathematical meanings?
4. Does the final primary receipt identify this exact r8 byte hash, all 23 audited declarations and only `{propext, Quot.sound}`? Inspect the audit source/log for candidate identity and omitted declarations; do not treat the prior successful command claim as independent verification.
5. Are holes, bypasses, unsupported claims, missing cases or source/model divergences present? State the specific falsifier and whether each finding is blocking, major or minor.

The reviewer may read the frozen inputs and governing locators, hash them read-only, and write only `tasks/agent-loop/inbox/native-integer-comparison-r41-review.md`. No Lean/Lake/checker, build, tests, source edits, cache writes, Git operations or additional agents. If an input hash differs, stop and report the mismatch.

Resource ceiling: reviewer at most 300 active seconds; Luna adjudication at most 300 seconds; one reviewer and one primary, no inherited R40 budget. Review output must record actual identity/session/model observations, exact inspected hashes, findings/disposition, omissions, duration and writes-stopped state. STOP at ceiling or missing frozen evidence.

No root import or integration is leased in R41. A future accepted integration must keep source/native realization, producers beyond the separately reviewed invariant, all other primitives, full executor/inference A/B and production OPEN unless their own evidence closes them. Pending question directories remain untouched and uncommitted.
