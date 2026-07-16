# Per-demand exact solve snapshot Stage 2 Slice C

Date: 2026-07-16

Status: **performance release gate failed; production activation must remain held**

This note records the final Stage 2 performance-gate verification required by
`2026-07-16-generalize-role-resolve-snapshot-spec.md` Section 8. It supersedes the preliminary
five-pair activation table in that specification. The approved thresholds are unchanged.

## Diagnosis of the original six production hits

The preliminary production run reported 6 exact hits and 606 full solves. Those six hits did not
include the expensive Markdown `proof` iteration-4 duplicate.

The independent always-full-solve characterization identified the six production-eligible repeats
exactly:

| Root | Repeated demands | Fresh-solve time represented by the repeats |
| --- | --- | ---: |
| `std.text.str.word_prefix_ascii_or_slow_end` | `Add`, `Fold` | 82.636 us |
| `std.text.str.word_prefix_at` | `Add`, `Eq`, `Sub`, `Ord` | 134.649 us |
| **Total** | 6 cheap repeats | **217.285 us** |

The same characterization reconfirmed the intended `proof` witness:

- iterations 3 and 4 had equal constraint epoch, supplemental epoch, candidate generation,
  post-floor main, and repeated normalized demand;
- iteration 4 contained one exact repeat;
- that repeat's fresh Debug solve took 1.702520 seconds in this diagnostic run, versus the original
  release diagnosis of approximately 0.95-0.99 seconds;
- the `proof` root retained the expected large snapshot shape and peaked at 20,653,144 Debug-proxy
  bytes; and
- every `proof` solve boundary had 33 pending session analysis work items.

The false miss came from Stage 2 production wiring. `GeneralizeRoleSnapshotRoot::boundary` rejected
every boundary with `pending_analysis_work != 0`. Stage 1 deliberately observed that queue length
but did not use it as an eligibility guard: the pure recursive solver cannot read the session
analysis queue, and its complete mutable inputs are already covered by `E/A/M/D/C` plus drained
constraint work and events. The extra production-only guard therefore rejected the target without
adding a correctness witness.

The narrow fix removes the session analysis queue from production eligibility while preserving the
constraint-work and constraint-event drain guards. A regression assertion now requires the
production Markdown run to retain the large characterized snapshot and exercise more than 100
exact hits. After the fix every release Markdown run reported 146 hits and 466 full solves, with a
20,653,144-byte peak, proving that the expensive `proof` snapshot now reaches production lookup.

## Large-entry cost diagnosis

Temporary release instrumentation timed the large entry directly, then was removed:

| Operation | Measured cost |
| --- | ---: |
| First large retain: 1,686,199-byte entry Debug accounting | 3.319 ms |
| First large retain: snapshot clone | 0.928 ms |
| Large 18,962,596-byte retain: existing-demand search | 0.003 ms |
| Large 18,962,596-byte retain: Debug accounting | 76.013 ms |
| Large 18,962,596-byte retain: snapshot clone | 43.990 ms |
| Expensive exact hit: linear search and structural equality | 5.257 ms |
| Expensive exact hit: cached outcome clone | 32.593 ms |

The `entries.iter().find(...)` structural comparison is not consuming anything close to the saved
0.95-0.99-second solve. Retention accounting and cloning are material, especially the approved
Debug-size proxy, but the directly measured large-entry dimensions total about 162 ms. No lookup
representation or structural-equality redesign is justified by this evidence.

## Measurement method

A fresh uninstrumented release binary was built with:

```text
RUSTC_WRAPPER= cargo build --release -p yulang
```

Each observation was a fresh process using the no-cache runtime route:

```text
target/release/yulang [--generalize-role-snapshot-always-solve] \
  --std-root lib --no-cache --runtime-phase-timings run FIXTURE
```

The fixtures were Markdown, HTML, `tests/yulang/support/empty.yu` for repository-std-only, and
`examples/showcase.yu`. Ten pairs were measured per fixture. Odd pairs ran enabled then
always-solve; even pairs ran always-solve then enabled. The decision values are internal
`run.build_poly` and `run.analysis.role_resolution.generalize`. Positive percentages are
improvements. `run.total`, external wall time, and maximum RSS are supporting observations.

## Full paired distribution

### Yumark Markdown

| Pair | Build enabled | Build always | Build change | Role enabled | Role always | Role change |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 4.870 s | 5.653 s | +13.851% | 1.288 s | 2.055 s | +37.324% |
| 2 | 4.867 s | 6.389 s | +23.822% | 1.245 s | 2.259 s | +44.887% |
| 3 | 4.950 s | 5.684 s | +12.913% | 1.335 s | 2.058 s | +35.131% |
| 4 | 4.974 s | 5.781 s | +13.960% | 1.260 s | 2.068 s | +39.072% |
| 5 | 5.807 s | 6.399 s | +9.251% | 1.591 s | 2.309 s | +31.096% |
| 6 | 4.714 s | 5.656 s | +16.655% | 1.264 s | 2.009 s | +37.083% |
| 7 | 4.608 s | 5.638 s | +18.269% | 1.174 s | 2.091 s | +43.855% |
| 8 | 4.689 s | 6.113 s | +23.295% | 1.182 s | 2.231 s | +47.019% |
| 9 | 4.487 s | 6.035 s | +25.650% | 1.189 s | 2.170 s | +45.207% |
| 10 | 5.189 s | 6.104 s | +14.990% | 1.423 s | 2.323 s | +38.743% |

### Yumark HTML

| Pair | Build enabled | Build always | Build change | Role enabled | Role always | Role change |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 1.247 s | 1.335 s | +6.592% | 19.1 ms | 13.0 ms | -46.923% |
| 2 | 1.217 s | 1.373 s | +11.362% | 17.1 ms | 13.6 ms | -25.735% |
| 3 | 1.237 s | 1.200 s | -3.083% | 17.8 ms | 12.6 ms | -41.270% |
| 4 | 1.184 s | 1.240 s | +4.516% | 16.5 ms | 13.6 ms | -21.324% |
| 5 | 1.214 s | 1.220 s | +0.492% | 18.0 ms | 12.4 ms | -45.161% |
| 6 | 1.228 s | 1.222 s | -0.491% | 18.1 ms | 13.5 ms | -34.074% |
| 7 | 1.259 s | 1.182 s | -6.514% | 17.6 ms | 12.5 ms | -40.800% |
| 8 | 1.269 s | 1.236 s | -2.670% | 18.1 ms | 13.0 ms | -39.231% |
| 9 | 1.234 s | 1.235 s | +0.081% | 17.3 ms | 13.3 ms | -30.075% |
| 10 | 1.288 s | 1.198 s | -7.513% | 20.5 ms | 14.0 ms | -46.429% |

### Repository std only

| Pair | Build enabled | Build always | Build change | Role enabled | Role always | Role change |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 1.249 s | 1.091 s | -14.482% | 13.2 ms | 7.5 ms | -76.000% |
| 2 | 1.134 s | 1.051 s | -7.897% | 12.1 ms | 7.9 ms | -53.165% |
| 3 | 1.378 s | 1.217 s | -13.229% | 15.2 ms | 8.3 ms | -83.133% |
| 4 | 1.068 s | 1.144 s | +6.643% | 11.7 ms | 8.4 ms | -39.286% |
| 5 | 1.166 s | 1.054 s | -10.626% | 13.7 ms | 7.7 ms | -77.922% |
| 6 | 0.989 s | 1.007 s | +1.827% | 10.2 ms | 7.6 ms | -34.211% |
| 7 | 1.054 s | 1.067 s | +1.218% | 10.0 ms | 7.4 ms | -35.135% |
| 8 | 1.085 s | 1.047 s | -3.629% | 10.7 ms | 7.2 ms | -48.611% |
| 9 | 1.049 s | 1.035 s | -1.353% | 10.4 ms | 7.5 ms | -38.667% |
| 10 | 1.000 s | 1.038 s | +3.661% | 10.3 ms | 7.8 ms | -32.051% |

### Showcase

| Pair | Build enabled | Build always | Build change | Role enabled | Role always | Role change |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 1.084 s | 1.144 s | +5.245% | 11.0 ms | 8.6 ms | -27.907% |
| 2 | 1.139 s | 1.130 s | -0.796% | 11.6 ms | 8.4 ms | -38.095% |
| 3 | 1.124 s | 1.063 s | -5.738% | 12.4 ms | 8.0 ms | -55.000% |
| 4 | 1.101 s | 1.134 s | +2.910% | 11.5 ms | 8.4 ms | -36.905% |
| 5 | 1.143 s | 1.131 s | -1.061% | 12.5 ms | 8.6 ms | -45.349% |
| 6 | 1.345 s | 1.131 s | -18.921% | 13.4 ms | 8.4 ms | -59.524% |
| 7 | 1.264 s | 1.233 s | -2.514% | 12.5 ms | 8.1 ms | -54.321% |
| 8 | 1.190 s | 1.130 s | -5.310% | 11.4 ms | 8.1 ms | -40.741% |
| 9 | 1.254 s | 1.198 s | -4.674% | 12.8 ms | 8.6 ms | -48.837% |
| 10 | 1.216 s | 1.210 s | -0.496% | 12.2 ms | 9.0 ms | -35.556% |

## Means, telemetry, budgets, and gate result

The gate compares arithmetic means of the mode observations, not the mean of the displayed paired
percentages.

| Fixture | Enabled build | Always build | Build change | Enabled role | Always role | Role change | Gate |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| Yumark Markdown | 4.9155 s | 5.9452 s | **+17.320%** | 1.2951 s | 2.1573 s | **+39.967%** | Pass: >=10% build and >=35% role |
| Yumark HTML | 1.2377 s | 1.2441 s | +0.514% | 18.01 ms | 13.15 ms | -36.958% | Pass: no build regression |
| repository-std-only | 1.1172 s | 1.0751 s | **-3.912%** | 11.75 ms | 7.73 ms | -52.005% | **Fail:** exceeds 2% bound by 1.912 points |
| showcase | 1.1860 s | 1.1504 s | **-3.095%** | 12.13 ms | 8.42 ms | -44.062% | **Fail:** exceeds 2% bound by 1.095 points |

The corresponding enabled/always mean internal `run.total` values were 5.1823/6.2114 seconds,
1.5076/1.5160 seconds, 1.2446/1.2040 seconds, and 1.3719/1.3323 seconds. Mean external wall was
5.196/6.223 seconds, 1.512/1.520 seconds, 1.250/1.208 seconds, and 1.376/1.337 seconds. Maximum RSS
was 527,424/447,468 KiB, 218,300/218,296 KiB, 202,472/202,640 KiB, and
205,856/205,912 KiB respectively.

Telemetry was constant across all ten runs of each mode:

| Fixture | Enabled hits | Enabled full solves | Always full solves | Peak entries | Peak Debug bytes | Cap fallback |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Yumark Markdown | 146 | 466 | 612 | 6 | 20,653,144 | 0 |
| Yumark HTML | 145 | 464 | 609 | 6 | 452,994 | 0 |
| repository-std-only | 145 | 429 | 574 | 6 | 30,990 | 0 |
| showcase | 148 | 440 | 588 | 6 | 30,990 | 0 |

All fixtures stayed below the approved 64-entry and 128-MiB proxy caps. The overall release gate
still fails because each individual control fixture must satisfy the 2% no-regression bound.

The control role phases consistently show 3.71-4.86 ms of absolute cache overhead while admitting
145-148 cheap exact hits. End-to-end observations are noisier than that mechanism cost, but the
approved arithmetic-mean decision cannot discard unfavorable samples or substitute a robust
statistic after seeing the result. A cheap-demand admission policy might avoid this overhead, but
none is part of the approved exact-cache design. A size or timing threshold selected from these
fixtures would be a new policy requiring its own design, adversaries, and complete gate rerun; it is
not a narrow correction justified inside Slice C.

## Verification and recommendation

Verification after the false-miss fix:

- the three focused cache unit tests passed;
- isolated production/always-solve Markdown and HTML parity passed, including the new large
  Markdown snapshot witness;
- the independent nine-case audit passed with 1,019 would-be hits, 1,019 exact matches, and zero
  result, disposition, state-delta, or full-path mismatches;
- the release build completed without warnings;
- all 80 release processes in the paired campaign completed successfully; and
- the full infer lib suite finished with 831 passed and only the five pre-existing
  `mark_expr_block_*` `DefId(64)` versus `DefId(63)` failures.

The narrow false-miss fix is valid and makes the intended Markdown optimization real, but the
approved Stage 2 release gate is **not met**. Production activation from `61eb2b7f` should not be
pushed as the default. Keep the always-full-solve path as the production default, retaining the
exact implementation, independent oracle, telemetry, and false-miss regression for a separately
designed cheap-demand admission follow-up. No Stage 3 work is authorized by this result.
