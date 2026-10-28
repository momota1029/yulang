# NATIVE-LAUNCH-PROJECTION/r6 outcome — CLOSED_INCOMPLETE

**Status: CLOSED_INCOMPLETE / REJECTED.** Fresh independent review rejected the frozen package. Under the R6 contract, rejection authorizes no conditional Rust/Lean checks and no source revisions. The larger inference/executor, effect-hygiene, source/native and production goals remain OPEN.

## Authority and inputs

- Contract: `tasks/agent-loop/sprints/native-launch-projection-20261028-r6.md`, SHA-256 `01236acb3ef9134788e58aa888ec7d498ddd24fa9f64250c4f1fc2837f03034a`.
- Amendment 01: `tasks/agent-loop/sprints/native-launch-projection-20261028-r6-amendment-01.md`, SHA-256 `770332723483bb646936c71eb4bf7e83e9dfaf5ee6cf9898ff0bbefe98ff5296`.
- Baseline: clean isolated source snapshot from `7b3ad7074`; proof/core source reads resumed only from amendment-pinned immutable proof inputs.
- R5: closed rejected reference only; no R5 proof or source output was promoted.

## Frozen outputs

| Artifact | SHA-256 |
|---|---|
| Isolated `candidate_scheme.rs` | `c79b136dd033a4d0e3f1664be670fda0c538866baa05a20c273d69a1927ead0d` |
| Isolated `candidate_context.rs` | `19726ef8a6034a1b99f629021b6b7e97ec638f3c1d683206de3c6eac8025a2ec` |
| Isolated `candidate_extrusion.rs` | `e532e7228487e125a73576cb76b8bf17c065862b049bd8d6f8fa185bb77c54af` |
| Rust handoff | `ab4fc227328d2ad8e9081d3379778f5d99f10177462e4df616a9d8ba776b694d` |
| `NativeLaunchProjectionR6.lean` | `eb4c5c99fee13689b4c7ee4b9cf7668ec39416e3259ed826c44204c78fc7ea13` |
| Proof handoff | `2a4cb3c9e0af0fa354ce89b6b8305d9ff54f55889407f9001d1018bad4bdc4c4` |
| Astra core handoff | `c8ca2b528fcaf4b62c578535cfbe570db92dfa47cae5d1c025c0fd4b0072482d` |
| Independent review receipt | `4323f806ad9767f9da111dfca187b3866bb9bc54a203d6825ad85ea96007ebe3` |

Rust output is provisional test-only instrumentation. The proof output contains seven unchecked candidate terms; there is no composed `runPrefix` theorem or Idle/Some-to-Running theorem. No theorem types were checked or transitively axiom-audited.

## Independent review and disposition

Reviewer: `/root/native_launch_projection_r6_review`, registered `compiler_referee`, requested Sol/medium, observed model/effort UNKNOWN. Duration and CPU/RSS were not independently measured. Source bodies and governing contract were inspected before producer explanations. No checks, Git, builds, tests, Lean/Lake, formatter, descendants or source writes ran.

Verdict: **REJECT**. Findings:

1. **BLOCKING:** `candidate_extrusion.rs:753–754` passes `ExtrusionEndpoint` where the lane vectors require `u32`, `ValueEndpointKey`, or `EffectEndpointKey`, and returns an unwrapped lane value where `BoundKey` requires `ExtrusionEndpoint`. All eight macro expansions are affected.
2. **BLOCKING:** `candidate_extrusion.rs:787` constructs `BoundKey` with only the inner row/atom key; it omits the required outer `ExtrusionEndpoint::Value` or `::Effect`. This independently prevents the test build.
3. **major:** the Lean model uses replay undo capacity where native code samples `route_journal.value_rows.capacity()`. Under the probe flag, native code can panic after ledger/counter/sample publication and before its completed trace; the candidate omits that intermediate error prefix. Exact resource/callback source correspondence remains unproved.
4. **minor:** `current.json` retained a stale amendment lease hash `0db2b4f8…`; authenticated frozen amendment and producer ACK hash is `77033272…`. Corrected in closeout synchronization.

The reviewer also disclosed one hash-only script that initially resolved nine dependency paths against root files. It interpreted no root source body and made no writes. The reviewer repeated authentication using explicit isolated paths; all intended snapshot pins matched. The mistaken hashes were discarded. This deviation is recorded, not waived.

The bounded observer does address the R5 stale-readback and handle-link gaps by recording invocation/handle at actual begin/return, joining those records, and rereading the current physical row/lane. The ordinary module freshening path reaches the driver. The raw-transformer mutation restores the original value before asserting rejection. These remain source observations; the fixture was not executed.

## Proof and parent boundary

The proof candidate represents resource writes and failure paths but remains abstract at native callback correspondence. Its first unmodeled **launch owner** is `clear_diagnostic_scratch` (`lib.rs:15934`, called from `14196`); exact resource realization is open earlier. Seed, enqueue and passive receipt are distinct later owners and are not closed.

The original `SourceProblem.InferenceSoundness` quantifiers and separate `SourceProblem.NativeCorrespondence` are unchanged. No concrete source judgment, shared witness, full-language correspondence, semantic approval or production claim closes. Immutable-birth qualification and annotation-effect hygiene remain governing and open.

## Execution, records, and closeout

Both producers froze all leased outputs. Astra stopped on the read/write collision after three stages. Reviewer and producers report no prohibited compiler, Cargo, Lean/Lake, test, build, formatter or Git checks. Review found no basis for allowing the contract's conditional checks after rejection; none ran. Worker duration and CPU/RSS measurements remain UNKNOWN where stated.

`current.json` records the rejection, STOPPED workers, exact frozen receipts, and unchanged unknown/quarantined reservations. Resolved R6 leases are transferred to the R6 history archive; unknown and quarantined identities/paths remain present. `python3 tools/agent_sprint.py check` is run only for closeout record validation; it is not source or compiler evidence.
