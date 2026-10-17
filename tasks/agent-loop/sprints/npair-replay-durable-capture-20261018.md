# Sprint `npair-replay-durable-capture-20261018`

Status: CLOSED-REVIEWED-PARTIAL. Branch
`research/simple-sub-intrusion`. Parent `CHOOSE-SOURCE-2 /
RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN; original conditions closed0.
Baseline: `551773b8692540a55f69014c2194ff081331b2cb`. Astra0; no rollover.

## Fixed outcome

The previous reviewed companion/harness run exited0 and reached candidate
inference, but the execution tool truncated stdout before Replay rows could be
classified. The old complete transcript is unavailable. Re-run the **unchanged
reviewed bytes** exactly once in this fresh sprint, redirect stdout and stderr
directly to durable leased files, and classify a demand-bearing Replay by
joining its `call` index to the authenticated `candidate.source_call[index]`,
matching native root and ordered endpoints. If the complete capture has no such
row, record that exact result without asserting semantic impossibility.

This is a new authorized invocation; it does not revive or retry the retired
prior sprint command. It makes no compiler, fixture, test, semantic or expected
output changes. Original theorem closure remains0.

## Exact leases

1. **Luna implementation/runtime — 300s.** Writes only:
   - `tasks/agent-loop/runtime/20261018-receive-applied-durable.stdout.log`
   - `tasks/agent-loop/runtime/20261018-receive-applied-durable.stderr.log`
   - `tasks/agent-loop/runtime/20261018-receive-applied-durable.meta.json`
   - `notes/progress/2026-10-18-receive-applied-durable-capture.md`
   - `tasks/agent-loop/inbox/20261018-receive-applied-durable-capture.md`

   Related stages: prepare capture directory/metadata (60s), wait for preflight
   review and run the one command (120s), freeze logs and receipt (120s).
   Do not alter the reviewed example or fixture. Do not use a pipeline, `tee`,
   filtering, or truncated terminal capture.

2. **Sol proof lane — 120s.** Writes only:
   - `notes/theory/2026-10-18-receive-applied-replay-attribution.md`
   - `tasks/agent-loop/inbox/20261018-receive-applied-replay-attribution.md`

   Prepare the exact attribution criterion before execution (30s), then inspect
   the frozen complete logs and prove the row-to-source/native join (90s). A
   printed observer summary alone is insufficient.

3. **Fresh independent compiler review — 180s, read-only.** Review the exact
   pinned dependencies and redirection/metadata plan before execution (60s),
   then independently check the frozen log integrity and attribution snapshot
   (120s). No commands, edits, descendants or self-review.

4. **Luna primary 60s; reserve60s; total720s.** Primary owns current state,
   exact dispatch, integration and Git. The sole permitted harness invocation,
   only after preflight CLEAN and a fresh measurement of at least120s capacity:

   ```sh
   timeout 120s env YU_CALL_REPLAY_OBSERVER=1 cargo run --offline --manifest-path crates/yu-solver/Cargo.toml --example research_source_registration --features shadow-apply-candidate > tasks/agent-loop/runtime/20261018-receive-applied-durable.stdout.log 2> tasks/agent-loop/runtime/20261018-receive-applied-durable.stderr.log
   ```

   Run exactly once. Preserve the actual exit code. Record UTC start/end,
   working directory, environment switch, byte counts and SHA-256 for both logs
   in the metadata file. If the invocation fails, times out, capture is
   incomplete, a dependency pin mismatches or budget falls below120s, stop with
   the exact limitation; no retry. No other build/test/compiler command.

## Frozen inputs

Rehash before reliance. Prior parent-sprint rev2 contract:
`12e92e74afd24104e28cd17584658d668bf055df8d4ad6e3b0a3bfb1dbd8f19a`.
Prior proof and implementation review were CLEAN on the unchanged source
snapshot. These hashes protect that snapshot; the fresh review independently
checks the capture plan and the final transcript.

| Path | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_context.rs` | `46f0b74c8aa942c629a456272c3ae601827f1794b25d7034479edee62bc13e4f` |
| `crates/yu-solver/src/candidate_source.rs` | `1a65c7afb02a4afd538a34c34086108959579e06aafe8fbcab8ad6a6b3a65f3e` |
| `crates/yu-solver/src/candidate_call.rs` | `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479` |
| `crates/yu-solver/src/candidate_scheme.rs` | `ea48b5ec33ba9724bb761e3e04aa05cbf3eea22641830c442c8ecdcde54243d6` |
| `crates/yu-solver/src/shadow_apply.rs` | `51d1d1534d86181dce6caf0638f5c55e7c3bad6d764c3da5c4c9af10421335ac` |
| `crates/yu-solver/src/lib.rs` | `ddd1395877d4a76e27a1dcf32af90c6fcb0e58c739610a0115c03955628350e1` |
| `crates/yu-solver/src/tests/candidate_graph_call.rs` | `21c555b57a8684c9f8971e9180ac0ee732dc7a82834db606241653869987f55b` |
| `crates/yu-solver/examples/research_source_registration.rs` | `eb7e5aae0f29d9277ba191dc965918a6110eca8f054417aa44bbb0cec1f414e6` |
| `tasks/agent-loop/fixtures/20261018-receive-choose-applied.yu` | `7d7ad10d00773ecef583c53a1d546737dbf92daf75a9637f45c03798eb893fad` |
| `tasks/agent-loop/fixtures/20261017-receive-choose.yu` | `969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0` |
| `notes/theory/2026-10-18-receive-applied-source-correspondence.md` | `e636422256e63af9cb04b8962f95fd0fbc845283aabcc7635c07fe5483d4e503` |
| `tasks/agent-loop/inbox/20261018-receive-applied-source-correspondence.md` | `5401a12dccbbe997734bc6887c30e0d8b22f74de83271bd256d491a438dbfac9` |
| `tasks/agent-loop/sprints/npair-applied-fixture-replay-observation-20261018.md` | `12e92e74afd24104e28cd17584658d668bf055df8d4ad6e3b0a3bfb1dbd8f19a` |

## End condition

Freeze capture hashes and fresh final review. Report whether a matching
demand-bearing Replay row exists in the complete capture, the exact source and
native join, or the exact obstruction. Original theorem conditions closed0;
parent remains OPEN. No budget rollover.

## Luna closeout rev2

The one authorized invocation exited0, with direct durable stdout/stderr
capture. The final independent review was CLEAN: all 13 direct dependency pins
and all seven frozen artifact hashes matched. The complete capture contains no
typed `candidate.call_replay` row. The companion `source_call[3]` authenticates
all eight checks and maps to native demand root379, but no Replay row exists to
join to that root. This is a bounded observation about this run; it does not
show semantic impossibility or consumer coverage. The observer can silently
stop on stderr write failure and omits entries with absent demand.

Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN;
original conditions closed0. No code, fixture, test or semantic change was
made. The prior focused suite remains 5/5 from its separate reviewed sprint.
Workers are STOPPED; exact artifacts remain FROZEN. Runtime300 + proof120 +
review180 + Luna primary60 = 660/720 seconds charged; reserve60 expires and
does not roll over.

Next discriminating work: trace existing demand retention and child scoped
demand availability through their owners, then determine from existing rules
whether the absent row is caused by missing retained dependencies or by the
consumer's scope/availability path. Do not infer either cause from this run.
