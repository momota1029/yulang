# Cycle54: scalar-preserving source endpoints

## Recovery and bounded result
Scheduled start: 2026-11-09T21:27:19Z. Deadline: 21:52:19Z.
The original worker completed local implementation f62a30196e923478fe93df2fd7de53a13bc20113 and focused verification, then stopped before publishing a result or report. At 21:48Z the remote branch still pointed to startup commit d9f1e243b1d50aeadbdd70f85048ee0f6df6aa44 with a stale running heartbeat. No concurrent Yulang worker was active. Recovery retained the existing checkout and cache and changed no implementation code.

The bounded scalar-preserving endpoint and flat graph-inspector bridge is closed.
Ordinary int, bool, str and unit remain distinct, including actual str rather than an int or nominal surrogate. Endpoint variants are finite; independent Meaning does not invoke detect or materialize. Known scalar observations are exact for paired evidence under an explicit ordinary model. Scalar observations persist through atom inclusion under a model of the later state, and endpoint evaluation is invariant under equal atom membership.

For every finite positive-string/equality source table, initial problem and supplied finite update list, actual incremental string readout is equivalent to all independent original source models forcing string. Unknown readout is equivalent to two source models assigning inequivalent types. These source-fragment statements need no caller-supplied consistency or successful-scope premise. They connect to the actual checked Index producer, cycle53 occurrence diagnostics, and the existing graph head inspector.

## 22 audited declarations
CommonRoleScalarSourceEndpoint:
eval_present, eval_sound, observe_exact, observe_detect, observe_unknown,
scalar_persists, eval_order_independent, materialize_string_iff,
solve_string_exact, solve_unknown_exact, solve_checked_iff, diagnostic_waiting_iff.

CommonRoleScalarSourceInspection:
code_injective, graph_scalar_exact, graph_unknown_exact, inspect_scalar_exact,
inspect_evidence_exact, snapshot_unknown_exact, solve_inspect_string_exact,
solve_snapshot_unknown_exact, original_diagnostic_snapshot, recorded_scalar_inspected.

The first group covers independent observation soundness, paired-evidence completeness,
finite variants, order/inclusion properties, and exact source/producer/diagnostic bridges.
The second covers injective scalar codes and exact graph/inspector readout, source-model
semantics, occurrence diagnostics, and a regression for each scalar base.

## Verification
Recovered exit files for focused build, final focused build, trust-0 audit and diff gate all contained 0.
Recovery independently reran:
- cd lean && ELAN_HOME=../../elan timeout 60 ../../elan/bin/lake build --wfail Yulang.CommonRoleScalarSourceEndpoint Yulang.CommonRoleScalarSourceInspection
  Exit 0: Build completed successfully (295 jobs).
- cd lean && ELAN_HOME=../../elan timeout 60 ../../elan/bin/lake env lean --trust=0 /tmp/cycle54-audit.lean
  Exit 0: all 22 declarations use only propext, Classical.choice and Quot.sound; code_injective uses no axioms.
- bash tools/verify-lean.sh . origin/integration/m1-final --no-build
  Exit 0: diff checks PASS. No removed Lean lines, forbidden proof shortcuts or lake config changes.
- git diff --check
  Exit 0.

The new modules are imported by Yulang.lean, and all 22 declarations are registered in Audit.lean.
Full lake build, full Audit and broad axiom gate were not run. No CI pass is claimed.

## Publication
Recovered result commit: 0dfef90eb7551e73fcde1d3759dae0dbf6181fa8.
Result tree: 8b71bdd483709695f2fc7c3887c865b86ecb16d2.
All seven implementation files were uploaded as individual blobs. Each returned blob SHA matched the local file. A SHA-only tree based on the remote startup tree matched the entire verified local implementation tree exactly. Publication used a non-force update with expected head, on work/dots-main only. This report and the completion heartbeat are separate bookkeeping; no integration branch was changed.

## Limits and remaining work
This is an additive observation adapter, not a new role matcher. The finite positive-string/equality source carrier and externally supplied finite updates remain explicit fragment restrictions, not language rejection rules. bool/unit observations are preserved without asserting support by the separate Roles.Term producer.
The graph is flat and retains original occurrence slots. Recursive graph construction, unknown alias canonicalization, general candidate applicability, declaration-generated child/request construction, dictionaries and language-level four-way classification remain unproved.
General B4 still has five open bridges: source_boundary_adequate, generated_work_closed, saturate_terminates_and_closes, saturated_frontier_exact, resolve_dictionary_order_sound. This closes a named sub-boundary, not any entire general bridge.
The design records consultation of work/dots-audit X13-X17 and C3-PARENT plus spec 6.3. Recovery ran no new Yulang2 instance and made no semantic decision.
Existing workspace/cache retained; 48 GB free. No new worktree or cache copy.
