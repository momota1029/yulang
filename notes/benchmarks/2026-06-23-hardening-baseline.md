# 2026-06-23 Hardening Baseline

This note records the first baseline after `802a1c1c3db3` (`Record hardening metrics inventory`).
The goal is not to optimize. The goal is to keep a comparable snapshot for future solver hardening work.

Measured at `2026-06-23 18:01 JST` on the local WSL2 environment.
All long commands used an outer `timeout`.

## Commands

```sh
timeout 180s cargo run -q -p yulang -- --std-root lib check-poly-std examples/showcase.yu
timeout 180s cargo run -q -p yulang -- --std-root lib check-poly-std-in examples/showcase.yu std.control.var.ref
timeout 240s cargo run -q -p yulang -- --std-root lib --runtime-phase-timings --no-cache run --print-roots examples/showcase.yu
timeout 300s bench/static_analysis_bench.sh --repeat 3 --infer-only examples/showcase.yu
```

Raw command output was captured under `/tmp/yulang-hardening-baseline-2026-06-23/` during measurement.

## Static Check: `check-poly-std examples/showcase.yu`

High-level:

```text
files: 36
collect: 74.2ms
infer: 2.854s
summarize: 2.1ms
total: 3.215s
```

Lowering / analysis:

```text
lower.index_csts: 15.0ms
lower.module_map: 35.4ms
lower.bodies: 881.8ms
lower.drain: 628.3ms
lower.resolve: 1.285s
analysis.route: 13.8ms
analysis.route_scc_events: 1.594s
analysis.route_scc_quantify: 1.207s
analysis.route_scc_instantiate: 385.2ms
analysis.work: 1.637s
analysis.work_apply_select: 1.186s
analysis.work_apply_select_typeclass_method: 1.018s
analysis.role: 265.7ms
analysis.role_solve: 250.2ms
analysis.quantify: 1.207s
analysis.quantify_generalize: 1.164s
analysis.instantiate: 383.9ms
analysis.instantiate_subtype_predicate: 366.6ms
```

Constraint work:

```text
constraint.drain: 996.8ms
constraint.drains: 17623
constraint.work_items: 91664
constraint.subtype_work_items: 91581
constraint.max_initial_queue: 126
constraint.max_work_items: 11159
constraint.lower_bounds_added: 72167
constraint.upper_bounds_added: 75252
constraint.lower_replay_inputs: 372491
constraint.upper_replay_inputs: 287494
constraint.lower_replay_enqueued: 372491
constraint.upper_replay_enqueued: 287494
constraint.lower_replay_var_var: 352835
constraint.upper_replay_var_var: 266371
```

SCC / role / instantiate:

```text
analysis.work_items: 4011
analysis.scc_event_batches: 3925
analysis.scc_events: 1931
analysis.scc_quantify_events: 553
analysis.scc_instantiate_events: 1096
analysis.scc_other_events: 282
analysis.scc_ready_component_checks: 2755
analysis.scc_ready_member_checks: 1666
analysis.role_passes: 9
analysis.progressed_role_passes: 4
analysis.generalize_iterations: 747
analysis.generalize_merge_restarts: 80
analysis.generalize_subtype_restarts: 50
analysis.generalize_role_restarts: 64
analysis.instantiate_event_runs: 805
analysis.instantiate_max_event_run: 126
analysis.instantiate_unique_targets: 292
analysis.instantiate_reused_target_events: 804
```

## Follow-up: Role Resolve Metrics Slice

After adding role resolve counters and moving post-work SCC routing out of
`analysis.work_*` timing, the same `check-poly-std examples/showcase.yu` smoke showed:

```text
infer: 2.615s
constraint.drain: 891.1ms
constraint.replay_enqueued: 659985
analysis.route_scc_events: 1.527s
analysis.route_scc_quantify: 1.167s
analysis.route_scc_instantiate: 358.6ms
analysis.work_apply_select_typeclass_method: 17.6ms
analysis.role_solve: 242.9ms
analysis.quantify_generalize: 1.125s
analysis.generalize_resolve_roles: 141.4ms
analysis.instantiate: 357.4ms
analysis.role_demand_count: 2323
analysis.role_resolve_demands: 481
analysis.role_resolve_candidate_scans: 3286
analysis.role_resolve_candidate_matches: 189
analysis.role_resolve_already_applied: 93
analysis.role_resolve_candidate_cache_hits: 717
analysis.role_resolve_candidate_cache_misses: 2569
```

The earlier `analysis.work_apply_select_typeclass_method: 1.018s` number included
post-work SCC routing and was also represented in `analysis.route_scc_events`.
With that double attribution removed, the typeclass method apply item itself is small;
the current static-analysis bottleneck is still `route_scc_quantify` /
`quantify_generalize`, followed by constraint replay drain and role solve.

## Focused Check: `std.control.var.ref`

This uses the same source set, but filters the report to `std.control.var.ref`.
It is useful when checking the `ref.update` public signature canary.

```text
files: 36
infer: 2.695s
total: 3.032s
constraint.drains: 17623
constraint.work_items: 91664
constraint.lower_replay_enqueued: 372491
constraint.upper_replay_enqueued: 287494
constraint.lower_replay_var_var: 352835
constraint.upper_replay_var_var: 266371
values: 1
typed lets: 1
missing schemes: 0
bodyless declarations: 0
stack schemes: 0
lowering errors: 0 local / 0 total
```

The filtered module has `stack schemes: 0`.
If this becomes non-zero around `std.control.var.ref.update`, inspect public evidence leakage before chasing performance.

## Runtime Smoke: `showcase`

Command:

```sh
timeout 240s cargo run -q -p yulang -- --std-root lib --runtime-phase-timings --no-cache run --print-roots examples/showcase.yu
```

Roots:

```text
run roots [25, [(3, 4, 5), (5, 12, 13), (6, 8, 10), (9, 12, 15)], "every left dominated", ["[ok] hello", "[err 404]", "..."], [111, 11, 101, 1, 110, 10, 100, 0]]
```

Timing:

```text
run.collect: 46.4ms
run.build_poly: 3.026s
run.specialize: 50.5ms
run.control_lower: 1.6ms
run.vm_eval: 253.0ms
run.control_validate: 348us
run.runtime_init: 103us
run.runtime_execute: 246.7ms
run.root_format: 42us
run.total: 3.379s
```

Selected runtime counters:

```text
run.expr_evals: 135413
run.apply_value: 38583
run.apply_closure: 15888
run.apply_continuation: 1655
run.force_thunk: 17999
run.force_continuation: 1655
run.effect_requests: 2464
run.catch_matches: 2464
run.continuations: 2464
run.continuation_invocations: 1655
run.continuation_capture_clones: 2464
run.continuation_invoke_clones: 1655
run.continuation_frames_cloned: 88254
run.continuation_marker_scopes_cloned: 126435
run.frame_allocs: 11539
run.max_continuation_frames: 31
run.request_resume_steps: 12173
run.marker_frame_calls: 107417
run.marker_frame_request_closes: 64434
run.marker_scope_frame_touches: 394614
run.marker_scope_max_depth: 55
run.instance_eval: 275
run.instance_hits: 270
run.instance_misses: 5
run.path_prefix_checks: 73503
run.path_eq_checks: 6706
run.active_add_scans: 62001
run.active_frame_scans: 11502
```

## Bench Script: infer-only repeat 3

Command:

```sh
timeout 300s bench/static_analysis_bench.sh --repeat 3 --infer-only examples/showcase.yu
```

The first iteration includes extra cargo/build noise (`check` wall time `26.82s`), so the warmed comparison should use iterations 2-3.

Warmed iterations:

```text
iter 2:
  check: 0.66s
  collect: 7.7ms
  load: 51.0ms
  infer: 494.4ms
  bodies: 162.7ms
  drain: 121.4ms
  resolve: 205.5ms
  a_sccrt: 255.2ms
  scc_quant: 166.6ms
  scc_inst: 88.4ms
  a_work: 263.0ms
  w_asel_tc: 152.0ms
  a_quant: 166.4ms
  q_gen: 159.1ms
  a_inst: 88.2ms
  i_sub: 84.5ms
  c_drain: 210.8ms
  c_work: 91664
  c_lenq: 372491
  c_uenq: 287494
  total: 553.8ms

iter 3:
  check: 0.63s
  collect: 7.8ms
  load: 50.3ms
  infer: 472.6ms
  bodies: 149.8ms
  drain: 120.5ms
  resolve: 197.5ms
  a_sccrt: 248.1ms
  scc_quant: 162.6ms
  scc_inst: 85.3ms
  a_work: 255.8ms
  w_asel_tc: 147.4ms
  a_quant: 162.5ms
  q_gen: 155.5ms
  a_inst: 85.1ms
  i_sub: 81.7ms
  c_drain: 198.0ms
  c_work: 91664
  c_lenq: 372491
  c_uenq: 287494
  total: 531.3ms
```

Approximate warmed average:

```text
check: 0.645s
infer: 483.5ms
bodies: 156.3ms
drain: 121.0ms
resolve: 201.5ms
a_sccrt: 251.7ms
a_work: 259.4ms
a_quant: 164.5ms
a_inst: 86.7ms
c_drain: 204.4ms
total: 542.6ms
```

## Read This Before Acting On The Numbers

- This is a debug/local WSL2 baseline. Treat absolute timings as local reference, not release performance.
- Replay counts are stable and high:
  - lower replay enqueued: `372491`
  - upper replay enqueued: `287494`
  - lower var-var replay: `352835`
  - upper var-var replay: `266371`
- A future spike in replay counts is more important than a small timing fluctuation.
- `slot_count`, `row_variable_count`, `edge_count`, and max replay depth are still not named counters.
  Current proxies are compact var counts, bounds added, replay enqueued, and max queue size.
- Do not add replay clamps or solver cutoffs as a performance fix. If these counts grow, inspect row-tail polarity,
  private evidence leakage, and same-boundary alias-cycle subsumption first.
