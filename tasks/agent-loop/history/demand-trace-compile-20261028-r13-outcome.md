# DEMAND-TRACE-COMPILE/r13 outcome

Disposition: **CLOSED_INCOMPLETE.** The reviewed focused Cargo run compiled and exposed the intended same-invocation capture/FreshUse diagnostic, but the fixture failed with `ReceiptMismatch`. The trace localizes a missing reconstruction-map entry. It does not establish the source law needed to repair that map, a source/native Call/shared-witness bridge, original theorem closure, or production readiness.

## Frozen inputs and candidate

- Contract SHA-256: `a0510c9b2aa41a2826925f7f5c7d6b653a7d56af1c51b4574614fbe5b8b2e9c1`.
- Inputs manifest SHA-256: `475b5eaaea90d7a5f66b52ebf6b3cf45969b9c4c1953dd00c5593c75332763ee`; 434 entries.
- Candidate `isolated/demand-trace-compile-r13/crates/yu-solver/src/candidate_scheme.rs`: `0ca44b920d30e0a596584c9c4ad5e2a61fdd9115fe1eaaf4346ff64d0776afef`.
- `shadow_apply.rs`: `8db4bae1b79959161b6b0dc4d516164b0e756eb8cbc73896bb4a4545a0b0ebf8`.
- Rust handoff rev2: `40229f9eb85e12bc90865e1997a299037dbb6990091356965ff4953504537953`.
- Independent final review: `tasks/agent-loop/inbox/demand-trace-compile-r13-review.md`.

The only source changes repair R12 instrumentation compilation: one format argument/format-slot correction and two test-only `Graph` initializer fields. Fixture, assertions, solver semantics, and expected behavior are unchanged.

## Cargo-1 and trace

The exact contracted command ran once with CPU affinity 0 and process-group monitoring. Cargo/rustc 1.95.0; exit **101**, wall **88.4893 seconds**, sampled CPU **45.84 seconds**, sampled process-group RSS **1,839,558,656 bytes** against **2,147,483,648 bytes**. The 120-second wall and RSS limits were respected. Stdout: 0 passed, 1 failed, 816 filtered out; stderr records successful compilation and test execution. Complete logs are retained at `isolated/demand-trace-compile-r13/logs/r13-cargo-1.*`.

Log SHA-256 values:

- argv `7361b29dc8d288dc2f1746fcf1c6793aef866d7fa8f956ba47843b5ad33e7aec`
- stdout `148a99a6453e583317fadbb43b24660060f3e5725816d27aeaed5a2bc0c4e199`
- stderr `caa03d84c01e3a0a16ddedfe4817cbe6b96636c5487f29356f74054f4d2ad84e`
- resources `c4f09502a3f51b88ab7d489a82fe3b2918741cce76eb1920f03bd4cad5a7b8d9`

Within invocation 1 and capture graph 3, latent-demand capture interns negative root `TermArenaBrand(1):264` at node 11. FreshUse in graph 3 reaches bound ordinal 3 and relation 8; its negative bound upper endpoint is the same root, with upper index 11. The printed demand matches at both sites: original call 0, use instance 0, output scope 1, input route 0. The source lookup prints Definition owner, expression 1, occurrence ordinal 2, but debug output omits their identity fields.

At FreshUse, `negative_formal_roots` has length 0. Root lookup returns `None`, so `candidate_scheme.rs:4658` returns `ReceiptMismatch` before antecedent import. The captured antecedent reports admission/emission heads 6 and `EvidenceCoverage { gaps: 56 }`. This is an authentic finite diagnostic of the current path, not complete evidence coverage or authorization for semantic repair. Graph 1 is a separate capture and is not used to join the graph-3 trace.

Source inspection explains the implementation seam: capture interns the latent demand endpoint at `candidate_scheme.rs:2773`, while publication later builds `negative_formal_roots` only from terms in `formal_domains` (`:2890–2901`). FreshUse requires the map entry (`:4651–4659`). This code relationship plus the runtime observation does not prove that every source-owned latent demand belongs in that map. The deferred-demand source law and original source/native shared-witness bridge remain OPEN.

Cargo-2 is **NOT_RUN**: Cargo-1 reached runtime failure, so the contract's compile-only correction condition does not apply. Lean is **NOT_RUN**; no independently justified theorem artifact was identified. Parent `YulangClosure.SourceProblem.InferenceSoundness`, source/native correspondence, effect hygiene, and production remain **OPEN**.
