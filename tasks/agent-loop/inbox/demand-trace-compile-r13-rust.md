# DEMAND-TRACE-COMPILE/r13 Rust handoff

Sprint / contract: `DEMAND-TRACE-COMPILE/r13`, `tasks/agent-loop/sprints/demand-trace-compile-20261028-r13.md`, SHA-256 `a0510c9b2aa41a2826925f7f5c7d6b653a7d56af1c51b4574614fbe5b8b2e9c1`.

Assignment / handoff: `DEMAND-TRACE-COMPILE-RUST/r13-rev2`.

Parent gate and source scope: original `YulangClosure.SourceProblem.InferenceSoundness`; R13 fixes only compilation defects in R12 test-only demand tracing. Source/native correspondence, deferred-demand source law, effect hygiene, and production remain OPEN.

Baseline / direct dependencies: baseline `7b3ad7074`; R12 close `69ebe0545`. R13 inputs manifest SHA-256 `475b5eaaea90d7a5f66b52ebf6b3cf45969b9c4c1953dd00c5593c75332763ee`, with 434 unique pinned entries and zero mismatches at intake. Parent R12 manifest SHA-256 `996d23a3f86541608bc7967658ceee9e29b128a95153fe6a60c26a00ef2ee05b` and R12 outcome SHA-256 `0708322e5657939276bb0827cd00431774cf56ee4a7b3bcdd4abfc530241e175` authenticated.

Role / worker / session: Luna/high implementation lane, `/root/demand_trace_compile_r13_implementation`, current `DEMAND-TRACE-COMPILE/r13` assignment. Requested model/effort: Luna/high. Observed model/effort: UNKNOWN (runtime metadata unavailable). No descendants.

Exact leases and authorship: only the following paths were written by this worker:
- `isolated/demand-trace-compile-r13/crates/yu-solver/src/candidate_scheme.rs`
- `isolated/demand-trace-compile-r13/crates/yu-solver/src/shadow_apply.rs`
- `tasks/agent-loop/inbox/demand-trace-compile-r13-rust.md`

Outcome class: implementation candidate; source-evidence instrumentation remains provisional.

Change: in `candidate_scheme.rs`, supplied `graph.boundary` in its corresponding positional format argument and moved `graph.nodes.get(graph.root)` into the `{:?}` slot. In `shadow_apply.rs`, initialized `r12_trace_graph_id: None` in the two test-only `Graph` literals at the prior R12 compiler error locations. Diff against R12 source consists of exactly this one argument insertion and these two test-field initializers. Fixture text, assertions, expected behavior, error kind, semantics, and solver paths were not changed.

Source constructors -> constraints -> propagation -> consumer/execution: no new inference behavior. This repairs only diagnostics needed for R12's existing test trace to compile; the source-to-constraint and native execution correspondence remains unresolved pending reviewed Cargo execution and primary trace analysis.

Prior evidence reused: R12 Cargo-1 stderr reported the missing `boundary` format argument, the `Option<&Node>` in a Display position, and missing `r12_trace_graph_id` in `shadow_apply.rs` test Graph literals at lines 4951 and 5064. R12 Cargo-1 failed during compilation; stdout was empty and the fixture did not execute, so no runtime result was produced. R12's source/semantic diagnosis was not accepted as a correspondence result. No withdrawn Simple-sub bypass was restored.

Artifact hashes / frozen review target:
- `candidate_scheme.rs`: `0ca44b920d30e0a596584c9c4ad5e2a61fdd9115fe1eaaf4346ff64d0776afef`
- `shadow_apply.rs`: `8db4bae1b79959161b6b0dc4d516164b0e756eb8cbc73896bb4a4545a0b0ebf8`
- this handoff hash is recorded after freezing the file bytes.

Checks and resources: no build, Cargo command, test, Lean run, or compiler check performed, as prohibited for this implementation assignment. Changes were inspected against the immutable R12 copies. Work stopped within the 400-second assignment limit; elapsed tool-work time was under 3 minutes (start observed at first local command, freeze at 2026-10-28 11:43 UTC). No scratch/generated paths were created. Cargo-1 remains pending independent source-first ACCEPT. Any instrumentation-local correction after Cargo-1 requires frozen delta and independent delta ACCEPT before Cargo-2.

Remaining premises / TODOs: Luna must review this frozen source correction, then run only the contract's Cargo-1 if accepted. If it compiles and executes, preserve the resulting trace or failure and establish same-invocation source/graph/bound/demand/use/antecedent evidence; compilation alone is not success. If Cargo-1 reports a remaining instrumentation-local compile issue, only one in-envelope correction and reviewed delta are allowed. No map insertion, semantic repair, retry after runtime failure, or claim of source/native closure is authorized.

Next related step inside envelope: independent source-first review of rev1, followed by Luna-owned Cargo-1 if accepted.

Mutual TODO: primary/Rust handoff request `R13-TRACE-EXECUTION-1`; original parent is `YulangClosure.SourceProblem.InferenceSoundness`; first missing evidence is a successful reviewed focused execution exposing the same-invocation trace or an honest new failure; source owner is Luna's candidate solver path; required inputs are the frozen R13 sources plus authenticated R12/R13 logs; proposed output is the primary-owned Cargo receipt and trace analysis; falsifier is compile/runtime/resource failure or inability to authenticate source occurrence against captured graph and consumer.

Writer stop: all writes ended at handoff freeze. Worker state STOPPED. No descendants or disposable scratch outputs.
