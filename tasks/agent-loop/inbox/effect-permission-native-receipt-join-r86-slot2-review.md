# R86 slot 2 output audit — FAILED, 30 declaration-level results retained

Reviewer: `/root/r86_repair_review` (`compiler_referee`), independent and
read-only. The reviewer did not run Lean, builds, tests or Git.

## Exact invocation and streams

Primary raw result:
`tasks/agent-loop/history/native-receipt-join-20261031-r86-slot2-raw-result.json`,
SHA-256 `bc62465e0fdeeeaab6bdd346fb4830f5dfee0058f0de4b146129438f1136582d`.
The reviewer reverified the committed authorization, candidate/handoff hashes,
reviewed 146,667-byte input hash, executable, command/settings and both streams.

- Exit code **1**, timeout **false**, elapsed **14.788 seconds**, peak child RSS **930,940 KiB**.
- Stdout: 178,056 bytes, SHA-256 `549877d9436f544e7451940d31f19eef444c2893962f28fc41c421ea6f0f9fed`.
- Stderr: 0 bytes, SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- Exactly 37 R86, 13 R84 and 11 R85 complete theorem type/axiom report pairs; 7 errors and 39 warnings.

## Failed declarations

These seven declarations have `sorryAx` recovery and are rejected:

| Declaration | Candidate line | Lean input line |
| --- | ---: | ---: |
| `readJoin_missing_attachment` | 185 | 2531 |
| `readJoin_missing_completion` | 193 | 2541 |
| `readJoin_ambiguous_completion` | 205 | 2553 |
| `readJoin_bad_guards` | 217 | 2566 |
| `readJoin_accepts` | 229 | 2579 |
| `readJoinInCuts_ambiguous_completion` | 425 | 2778 |
| `readJoinInCuts_accepts` | 439 | 2789 |

Each failed theorem depends on `[propext, sorryAx, Quot.sound]`. The helper
`singletonIndex_of_eq` itself is checked with `[propext]`, but each residual
goal still contains dependent `readJoin.match_3` over `n.origins[i]?`; the
supplied indexed-read equation does not reduce that matcher. These are proof
failures. They establish no source counterexample.

## Usable declaration-level reports

The other **30** R86 declarations have uncontaminated printed types and axiom
reports in this flattened input, under their stated conditional scope:

- No axioms (3): `completeClone_fields`, `fields_and_completed_determine_clone`, `singletonIndex_unique`.
- `[propext, Quot.sound]` (4): `readJoin_missing_origin`, `readJoin_ambiguous_origin`, `joined_R57_completed_false`, `readJoinInCuts_ambiguous_origin`.
- `[propext]` (23): `singletonIndex_empty`, `singletonIndex_multiple`, `singletonIndex_of_eq`, `completionIndices_single_clone`, `completionIndices_duplicate_clone`, `completion_index_read`, `completion_index_unique`, `joined_fields`, `joined_flags`, `joined_records_distinct`, `joined_completion_not_attached`, `joined_replacement_not_at_origin_index`, `joined_R57_rootDrain`, `joined_origin_blocks_R84_primitive`, `reachable_join_still_blocks_R84`, `readJoinInCuts_invalid`, `window_join_fields`, `window_origin_index_unique`, `window_completion_index_unique`, `window_join_completion_not_attached`, `window_origin_blocks_R84_primitive`, `origin_competitor_retained_in_cuts`, `completion_competitor_retained_in_cuts`.

All retained R84 and R85 reports are clean. No other project axiom,
`Classical.choice` or native-evaluation dependency appears.

## Final disposition

R86 is **INCOMPLETE / FAILED** under the committed gate: both calls were used,
the final invocation exited 1, and seven declarations contain `sorryAx`.
There is no third call. Preserve both raw receipts and the clean conditional
declaration-level reports without treating the overall reader gate as passed.
The source/native extraction gaps, distinct selector bridges, original A/B
and production remain open.
