# Sprint R322 — connect exact member selection to FreshUse

Status: RESULT_OBSTRUCTION; the unchanged Types sample still stops before member selection and successful inference.
Baseline: `research/simple-sub-intrusion`, current uncommitted worktree; R320/R321 source changes are carried forward.
Authority: existing user goal to run unchanged Yulang2 samples through ordinary inference/execution and close the proof path; preserve original sample text, expected output, semantics, quantifiers, and source domain. Converted unified design and proof companion remain governing sources.
Dispatch: degraded solo primary. The user's no-subagent instruction makes the repository selector and independent prover unavailable; no agent or reviewer is simulated.

## Bounded outcome

Use the exact `Display.say` MemberGraph captured by R321 and the authenticated source inventory/readback for the unchanged Types consumer to establish one exact `pair.say` member-use construction. The construction must preserve source member and implementation identities, FreshUse row sharing, receiver/result/effect roots, and every source where prerequisite. For `(Int, Str)`, it must retain the exact tuple Display implementation and its `Display int` and `Display str` prerequisites. The `[io]` annotation remains contravariant `[io,'e]`; passing `[state]` is allowed and must not be rejected as an effect violation.

Success is either (a) an ordinary candidate-session selection/application reaching successful inference for unchanged Types, or (b) a source-to-native traced precise obstruction showing which required premise still lacks a producer/consumer. A readback, standalone graph, or test alone is not theorem or source/native proof closure. Do not broaden into unrelated target syntax or close production gates.

## Relevant evidence and falsifiers

- R321 same-session graph capture: one exact `Display.say` MemberGraph, nested `show` FieldTail in FreshUse row layout, unchanged consumer `pair.say` retained and deferred.
- Existing readback matches the exact tuple target at `(Int, Str)` and records `a=int`, `b=str`, with exact source identities for both `Display` where clauses. Structural target match alone does not discharge prerequisites or establish stable selection.
- Falsify selection with a foreign source key, ambiguous applicable implementation, missing prerequisite, negative reachable bound, inconsistent shared row mapping, or any changed sample/output.
- Preserve `Display` contra-effect behavior: `[io]` supplies `[io,'e]`, so `[state]` is valid.

## Exact write leases

Only:

- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/candidate_source.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `crates/yu-solver/src/lib.rs`
- `tools/inference-playground/src/lib.rs`
- this contract, `notes/theory/2026-10-22-r322-member-selection-freshuse.md`, and `tasks/agent-loop/current.json`

R321 HIR/syntax changes are frozen inputs. Do not edit sample fixtures or pinned stdlib sources. Baseline hashes of the five code paths at R322 entry are recorded below.

| Path | SHA-256 at R322 entry |
| --- | --- |
| `crates/yu-solver/src/candidate_scheme.rs` | `651be259f6a113de2611db190a9de2ef11328d296714579aa48b3dd99968da70` |
| `crates/yu-solver/src/candidate_source.rs` | `052f291acd7f33af9736663ccc38c01cfde0dda7433cff7a0d6fab04767babfb` |
| `crates/yu-solver/src/shadow_apply.rs` | `967ef6fe3642fde7393f17d75349df9600f40da536fe7d288eb6e104e9bd7bcb` |
| `crates/yu-solver/src/lib.rs` | `8ae99bf187bf1c7a8ee69795fa5b7fea752e6c648073c10dc7609a4c0e668910` |
| `tools/inference-playground/src/lib.rs` | `aa8a72b82a3fb29c31482c895a18b044cdb6a27735513b66a99ee41fb00873bd` |

## Work and verification

Primary source/proof work: trace existing `FieldTail` construction, exact role/member inventories, implementation projection, where-bound producer/consumer, and FreshUse row restoration; carry every established construction back to the unchanged Types obligation. Independent review is unavailable under the user instruction, so label results solo/unreviewed.

Primary implementation: add only the smallest owner-local route from authenticated exact selection to candidate graph FreshUse and consumer constraints; preserve ambiguity/deferred behavior wherever inventory, bounds, or prerequisites are incomplete. Run focused solver tests, unchanged playground tests, HIR tests only if a frozen input issue is found, agent-sprint static checks, and `git diff --check`. One heavyweight Cargo process at a time.

Cap 2400 seconds, no carryover. Stop at successful unchanged Types inference, a precise source/native construction obstruction, the cap, or user STOP. Full source/native theorem, R149, Console, remaining samples, and production remain OPEN unless directly discharged by separate evidence under their preserved contracts.

## Result

R322 traced the exact owner-local seam and found the missing consumer. Source collection retains a `DeferredFieldTail` with authenticated role-member candidates and its four receiver/value/effect rows. Graph capture transports those rows; `prepare_candidate_fresh_use` computes and stores the four graph row indices. The only readers of `FreshUse.source_field_tail_obligation_rows` are its retained-byte/debug accounting and the test/readback layout path. No solver consumer uses those indices to freshen an implementation or role-default member, tie receiver/result/effect rows, or enqueue the nested FieldTail. Meanwhile `resolve_source_role_implementation_members` supplies exact override-member identities and explicitly does not select; `retain_role_implementation_members` stores this inventory but does not project implementation-member HIR into the candidate batch. The executor consequently leaves the obligation pending and returns `DeferredSelectionUnavailable`.

This is a precise source-to-candidate construction obstruction, not a source/native proof or successful sample result. It points to the next outcome: project exact implementation override member sources into candidate templates before solving, then implement the uniquely applicable FieldTail consumer that uses one FreshUse and discharges only complete exact where evidence. Preserve fail-closed behavior for ambiguity, incomplete inventory, unsupported targets, negative bounds, and missing prerequisites. Parent sample and theorem gates remain OPEN.

## Commit boundary

The user authorized committing coherent checkpoints and does not want permission prompts. `.git` was read-only at R321 entry, so commit/push availability must be checked at the preservation boundary; do not claim a commit if repository metadata remains unwritable.
