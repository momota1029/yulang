# Ordered Replay typed observer

Sprint `npair-original-c-compatibility-20261018`, rev2, contract SHA-256 `a48ee14722783e6598e782e405e880f9efe14ae8f5558bb0369834ea01d4affd`; baseline `29a7ace306cca2b3959ed752c859125b01f89543`.
Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN, closure 0.

## Implementation evidence

The private observer joins existing typed records without adding retained storage, public API, or solver/admission changes:

1. `Dependency::Replay` supplies exact `child/lower/upper` RelationIds and ordered `lower_input/upper_input: BoundKey`.
2. The child relation’s typed `ScopedFlow.demand` supplies `original_call`, `root`, and `use_instance`.
3. `original_call` indexes the same `candidate_calls.calls` vector observed by `source_call(index)`. The observer compares `demand.root` with that call’s retained `native.demand` and prints the equality check.
4. It validates each lower and upper relation pair against `bound_pair(lower_input)` and `bound_pair(upper_input)`, preserving the order and printing both checks.
5. Each matching Replay dependency is streamed as its own stderr row; there is no first-match selection, aggregate row selection, Debug-string parsing, or retained allocation.

The private `State::replay_demand_rows` iterator scans dependencies once, constant extra storage. It yields rows only for Replay dependencies whose child relation resolves to a typed scoped demand. Replays with no demand are intentionally omitted; the output is not complete over all Replay dependencies and does not report their count. Stderr truncation means missing output cannot establish absence or completeness. The observer is opt-in through `YU_CALL_REPLAY_OBSERVER`; disabled behavior adds only the environment check and no per-event scan/allocation. Output write errors are ignored so they do not change solve result.

The research harness still authenticates the exact received Apply/source_call by owner, occurrence, source keys, scope, checking occurrence and cause. Enabling the observer adds structural rows; it does not establish semantic Replay, `T_rho`, `At`, original-c membership, N-Transport, F1/FK1 or any parent condition.

## Review, checks and runtime boundary

Fresh compiler review was CLEAN on the exact three frozen implementation files. It confirmed the typed join, linear scan/constant extra storage, opt-in streaming and unchanged API/solver semantics; it also noted stderr truncation limits absence/completeness claims.

No Cargo command, tests, build or probe ran. At the last measured receipt, cap remaining was below 120 seconds; therefore the sole authorized command was not started. No identical-byte retry or other validation occurred.

Frozen code hashes:
- `candidate_context.rs`: `46f0b74c8aa942c629a456272c3ae601827f1794b25d7034479edee62bc13e4f`
- `shadow_apply.rs`: `d29d5f6488b5824eef5dc7902b70351b5bfae1ae3d7d014ec3629267443dbc83`
- `research_source_registration.rs`: `d76cbae29f5f095ffdb5068a49556149fe4a0fcc0f5d0702ff17ad71aed35f28`

Direct pins verified after rev2: HIR/compiler owners and design/theory dependencies all matched the contract. Parent original-c compatibility remains a separate open proof lane.

Requested model/effort Luna/high; observed UNKNOWN/UNKNOWN. Actual start 2026-10-17 21:28:39 UTC. No descendants or scratch paths. Fixture was not edited. Writer STOPPED after freezing note and inbox.
