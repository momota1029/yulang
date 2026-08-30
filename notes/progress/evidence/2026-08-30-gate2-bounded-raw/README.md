# Gate 2 bounded diagnostic provenance

[`samples.tar.gz`](samples.tar.gz) archives the eight `.stdout`, `.stderr`, and `/usr/bin/time -v`
`.time` files from the bounded Gate 2 diagnostic run. The original volatile directory was
`/tmp/yulang-gate2-bounded.oqdA6z`. The archive SHA-256 is
`41578caf323c38fd2809ea5b2b896924f814d544cc467a3112ec82d2aa5842d5`; it contains exactly the
24 raw files, including the eight empty stderr files.

The per-sample driver used this shape, with the recorded label and baseline/candidate binary
substituted for each invocation:

```bash
contention=$(ps -eo comm= | awk '$1=="cargo" || $1=="rustc" || $1 ~ /^yu_syntax-/ {print}')
if [ -n "$contention" ]; then
  printf 'INVALID_CONTENTION\n%s\n' "$contention"
  exit 97
fi
timeout --foreground --signal=TERM 60s \
  taskset -c 10 \
  /usr/bin/time -v -o "$root/$sample.time" \
  env YULANG_GATE2_SEQUENCE_ITEMS=10000 YULANG_GATE2_SEQUENCE_REPEATS=8 \
  "$bin" \
  --exact grammar::expression::tests::gate2_statement_sequence_performance_harness \
  --ignored --nocapture \
  >"$root/$sample.stdout" 2>"$root/$sample.stderr"
```

The fixed order was warm-up `B, C`, then measured `B, C, C, B, B, C`. All eight processes exited
zero. The driver observed no Cargo, rustc, or `yu_syntax-*` contention before the phase or any
sample.

Preflight commands also inspected the active Rust/Cargo toolchain, environment flags, allowed CPU
list, CPU 10/11 topology, governor availability, and current contention. Their output was retained
only in the execution transcript, not as a separate raw file. Every invocation was successfully
launched through `taskset -c 10`, but no independent per-child affinity observation was captured;
the `.time` files describe the inner `env ... <binary>` command and are not independent affinity
proof.

The driver recorded GNU `date --iso-8601=ns` timestamps in the Asia/Tokyo environment. The phase
started at `2026-08-30T23:28:55.734484614+09:00` and ended at
`2026-08-30T23:34:44.809904853+09:00`, for approximately 349.08 seconds. The 60-second `timeout`
was a per-invocation cap; actual timestamped phase duration establishes compliance with the
ten-minute phase budget.
