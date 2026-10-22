# Sprint R320 — operator owners in candidate dependency order

Status: ACTIVE; unchanged Yulang2 samples, R149 and parent proof gates remain OPEN.
Branch baseline: `a4127f9eb` on `research/simple-sub-intrusion`.
Authority: unchanged-sample user goal; R149; inference top-level principles; converted unified design and proof companion. Solo serial execution; dispatcher/prover callable tools are absent and user prohibits subagents.

## Parent and bounded outcome

R319 established the exact construction boundary: F0/F1 dependencies and candidate graph slots are binding-only, while module-expression schedules run after the binding SCC plan. An operator RHS expression captured afterward cannot supply a scheme to an earlier infix use.

Add a source-backed operator scheme owner to candidate dependency ordering. Keep `SourceOperatorOwner`, its exact provider `ExpressionRootId`, and each consumer occurrence distinct. Capture the provider candidate graph before each consumer, FreshUse it independently per operator occurrence, and emit two sequential Candidate Apply relations for each supported strict infix use in the unchanged sample set. Preserve operand order and all argument/result/effect ports. Do not synthesize `DefId`/`DefinitionOrderId`, route by spelling, or special-case a stdlib body.

This packet is a candidate implementation result only. Runtime/source-native correspondence, general principality, full operator forms, R149 and production remain OPEN.

## Required evidence and falsifiers

- Exact import owner -> provider expression root -> dependency node -> captured candidate graph.
- Dependency order makes the provider graph available before each retained consumer occurrence.
- Two uses create distinct FreshUse images; each infix keeps left then right operand and both Apply relations.
- Ordinary imported-name SCC/use routing remains intact.
- Reject a forged/foreign owner, missing provider root, wrong ordering, shared use image, dropped operand/effect endpoint, or a fake definition identity.

## Exact write leases and baselines

| Path | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `f34795ab6fd486355e41b987b1ef92887255f1b4814a29d9236704415598ea52` |
| `crates/yu-solver/src/scc.rs` | `8f3709ec9d52dc79767b6822eb4f671118a3f83814d2e9a9c748dfeac51e1f72` |
| `crates/yu-solver/src/candidate_source.rs` | `1127ade5b0c36758b262e27a3a4e8e060b5dacbd05162f240c1b0b21801972a8` |
| `crates/yu-solver/src/candidate_value_graph.rs` | `7f1d0859a8c139064fd7744cea805ca44ef5e94c28ff9777db51faf1d4dcad23` |
| `crates/yu-solver/src/candidate_scheme.rs` | `d057af438b2245be9ceae3027d48773ff6edfa1164612e9299f031c14a95a1f3` |
| `crates/yu-solver/src/candidate_call.rs` | `da085a4dcec8e8046b64edbb1ab8a2be2f889613d11b033504d65be6159aec91` |
| `crates/yu-solver/src/shadow_apply.rs` | `64885d9e38d2736fb605015d1a811fb4a72825e0dc1f9dac78dc80bde29ed4c8` |
| `crates/yu-solver/src/tests/candidate_graph_call.rs` | `7ff60ecb30e3815ba703463c87f053d66bf2d0c1833784dc64f993203fcdf5ef` |
| `tools/inference-playground/src/lib.rs` | `d35fba6e6db6b5529fc9107f81278a54776cc50fdece4370f2aa947e76c49cf2` |

Write only these paths, this contract/note, and `tasks/agent-loop/current.json`.

## Verification and resources

Primary-only cap 2400 seconds, charged R319 predecessor 540 seconds not carried. One heavyweight Cargo process at a time. Run focused solver tests, `cargo test -p yu-playground --lib`, `python3 tools/agent_sprint.py check`, and `git diff --check`. These checks are implementation evidence only, not theorem closure. Commit/push each coherent checkpoint when available; no force push.

Stop this packet at the bounded candidate correspondence, a concrete construction obstruction, cap, or user STOP. Keep original samples and parent quantifiers fixed.
