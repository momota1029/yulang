# N-pair observed Apply source evidence

Sprint contract: `tasks/agent-loop/sprints/npair-observed-apply-function-ingress-20261018-rev2.md`, rev2 SHA-256 `6792708386e9d977d8905716a2f79cc831fd5e37ad8f5e1d1b683919ddf8d0c8`. Baseline: `5c45c1807fc6f4fa495a2f0b85c4bdba1672820d`.

## One consumed source run

The only permitted command was consumed once:

```sh
timeout 120s cargo run --offline --manifest-path crates/yu-solver/Cargo.toml --example research_source_registration --features shadow-apply-candidate
```

It exited 0. Cargo reported a dev build in 1.60s. Output included existing dead-code warnings for `AssociationProvenance` fields, `replace_admission_root`, and `freshen_candidate_graph`. No other test, build, or probe was run. The task-clock start and total active elapsed/remaining time within the 720s cap were not recorded and are UNKNOWN; no process is active.

The run observed no structural parser recovery. HIR reported `UnsupportedExpression` over `received`'s expression range 372..382, but that diagnostic did not prevent `hir.local_source(received.definition_root())` from returning `Some`. The returned binding's LocalSource had three expressions and contained one outer Apply at occurrence 18, range 380..382. The candidate snapshot reported four collected source calls; the printed source call at index 3 had occurrence 18. Its source operands were `receive` at occurrence 19 (resolved to `ModuleDef(receive)`) and `f0` at occurrence 20 (resolved to `ModuleDef(f0)`). The candidate exposed native terms for callee `Term(brand1,index374)`, argument 375, result 376, demand 379, callee evaluation effect 381, argument evaluation effect 377, invocation effect 378, and application effect 380. The candidate observed the exact HIR and had no candidate conflicts.

Thus this run supports the narrow observed path `received` binding -> LocalSource -> Apply occurrence 18 -> collected source_call occurrence 18, with the source-level operands and native call endpoints printed in the same candidate solve. It also ran the pinned `source_call` accessors successfully. The run-time query did not enforce the rev2 strict equality checks for each Apply child, source key, and definition scope; it matched by owner-root and Apply-occurrence membership. It did not print the complete Function-child tuple or scoped dependency/relation-flow records. Those stronger checks and dumps were added only after this run and have not been executed. Therefore exact typed-endpoint/scope correlation, actual Replay dependency, lower/upper BoundKey ordering, and relation-fiber correlation remain unobserved.

## Query and fixture disposition

The currently frozen research example SHA-256 is `5525939261a25548f5694c06cef330dcf4e53079b6d5377b0a3cd87d4e2b8d12`. Changes after the consumed run add exact Apply-child/source/scope checks, print all four Function children, and dump aggregate scoped dependencies and relation flows. They are unexecuted; compile/runtime status is unknown. The public aggregate Debug views do not themselves establish a correlation to this source call's native handles, so no Replay edge is claimed.

The fixture was restored exactly to its pinned baseline SHA-256 `969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0`. Its temporary source change was limited to the authorized line `my received = receive f0`; no other fixture change remains.

The earlier source-path correction note (`notes/progress/2026-10-18-npair-actual-argument-source-path-correction.md`, SHA-256 `071b87b2e08acf6845de2b8fd16199fe0c84590abda5fc2f4bb41aae7fa39586`) supersedes the initial mistaken inference that the HIR diagnostic implied absence of a LocalSource. That correction is reused here. This source observation does not establish a production contribution or the original theorem. In particular, `s1 -> D`, same returned `R1`, whole parent closure, `eta`, `At`, N-Transport, and either ordered Replay input remain open.

## Stop receipt

Requested lane/model: Luna / implementer / high. Observed model and effort: UNKNOWN. The single command is consumed; no further run or speculative query work is authorized in this packet. No active process remains. Known disposable scratch files: none. The frozen example and restored fixture hashes above are the review targets; this bounded source-evidence result is stopped pending primary review and any separately authorized follow-up.
