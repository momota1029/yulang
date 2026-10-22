# Sprint R319 — source operator values in candidate inference

Status: ACTIVE; the unchanged Yulang2 samples, R149, and all parent proof gates remain OPEN.
Branch / baseline: `research/simple-sub-intrusion` at local commit `49ea4006c` (not pushed; current tree also contains the recorded R318 push-status update).
Authority: user goal for unchanged Yulang2 playground samples; Authoritative R149 §§Goal, Proposed behavior, Provisional adoption; inference top-level principles §§1–4; unified design §§2.2–2.3, 4.1–4.5, 5.1 and stages 4/10; proof companion §§2.16, 3–4, 7–8.
Dispatch: serial Luna primary. `next_action_selector` and `prover` are not callable in the live tool schema. The user explicitly prohibits subagents; no agent or independent review is claimed.

## Parent outcome and bounded objective

Parent outcome remains the original Yulang2 playground examples running through ordinary inference and execution, with their source/native proof obligations complete. R316 authenticates an imported operator declaration; R317 joins its RHS to the provider expression root; R318 includes that root in the candidate module world. The decisive missing path is now between the source-owned operator RHS, candidate generalization, and each consumer use.

Investigate and implement a source-authenticated candidate value path for the pinned strict infix `+` used by the unchanged Console sample. Reuse the exact `SourceOperatorOwner` and provider `ExpressionRootId`; do not resolve by spelling, synthesize a binding identity, or special-case the standard-library body. The consumer use must retain its own occurrence and operands and receive an independent use of the provider value. Trace both sequential application constraints through existing Candidate Apply machinery, preserving argument/result/effect ports.

This is candidate inference only. It does not claim runtime lowering, operator implementations for every fixity/laziness combination, source/native A/B closure, principality, or R149 completion. Existing behavior remains fail-closed outside the implemented candidate envelope.

## Success evidence and falsifiers

- Exact provider owner -> provider expression root -> generalized candidate value correspondence, with all identities tied to the same parsed source and pinned revision.
- The unchanged `say: 1 + 2` candidate path reaches a solved graph, and retained evidence identifies both operand applications and the original `+` use.
- Two uses of the same operator receive distinct use instances; ordinary imported-name Apply behavior remains intact.
- No source spelling fallback, fabricated `DefId`, dropped operand/effect edge, or mutation of the sample is accepted.
- A mismatch between the operator RHS scheme and its application shape, a shared use instance, or loss of source owner falsifies the candidate construction.

## Source/native and proof lane

Original accepted source and quantifiers stay fixed. Primary constructs the bounded source-to-candidate correspondence directly because no prover role is callable. The premises to trace are: the syntax-owned operator-use provenance; `SourceImportEnvironment::operator_owner_for_use`; R317 provider root join; definition/generalization/SCC ownership; per-use candidate initialization; two Apply relations; and the consumers of argument, result, and effect ports.

The abstract A/B obligations, full operator source-generation completeness, runtime correspondence, and independent review remain OPEN. Tests establish only the named candidate path, not a theorem. If the existing `DefinitionRootId`/`ClosedSchemes` boundary cannot express this owner without inventing identity, record the exact construction gap and keep the parent OPEN; do not narrow the language contract.

## Exact write leases

Baseline SHA-256 at packet issue:

| Path | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `f34795ab6fd486355e41b987b1ef92887255f1b4814a29d9236704415598ea52` |
| `crates/yu-solver/src/candidate_source.rs` | `1127ade5b0c36758b262e27a3a4e8e060b5dacbd05162f240c1b0b21801972a8` |
| `crates/yu-solver/src/candidate_value_graph.rs` | `7f1d0859a8c139064fd7744cea805ca44ef5e94c28ff9777db51faf1d4dcad23` |
| `crates/yu-solver/src/candidate_scheme.rs` | `d057af438b2245be9ceae3027d48773ff6edfa1164612e9299f031c14a95a1f3` |
| `crates/yu-solver/src/candidate_call.rs` | `da085a4dcec8e8046b64edbb1ab8a2be2f889613d11b033504d65be6159aec91` |
| `crates/yu-solver/src/shadow_f5.rs` | `b6a6c70da75329ff66cd9e6c0a2598a54cc8f0de7ba956f6f28b24616ca3a994` |
| `crates/yu-solver/src/shadow_apply.rs` | `64885d9e38d2736fb605015d1a811fb4a72825e0dc1f9dac78dc80bde29ed4c8` |
| `tools/inference-playground/src/lib.rs` | `d35fba6e6db6b5529fc9107f81278a54776cc50fdece4370f2aa947e76c49cf2` |

- `crates/yu-solver/src/lib.rs`
- `crates/yu-solver/src/candidate_source.rs`
- `crates/yu-solver/src/candidate_value_graph.rs`
- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/candidate_call.rs`
- `crates/yu-solver/src/shadow_f5.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `crates/yu-solver/src/tests/candidate_graph_call.rs`
- `tools/inference-playground/src/lib.rs`
- `tasks/agent-loop/current.json`
- this contract and `notes/theory/2026-10-22-r319-operator-candidate-value.md`

Read-only inputs include the R316–R318 receipts, `crates/yu-hir/src/module.rs`, HIR operator/source identities, the pinned R149 source bundle, and both converted Japanese design/proof Markdown files.

## Resources, verification, and stop

Solo primary cap: 2400 seconds; no carryover. One heavyweight Cargo process at a time. M1 implementation/proof-conformance audit by primary only; no independent review is available under the user's no-subagent instruction. Run focused solver/playground tests and `cargo test -p yu-playground --lib`; run `python3 tools/agent_sprint.py check` and `git diff --check` after record synchronization.

Commit and push each coherent result when Git metadata/network access permits. The prior R318 commit is one commit ahead of `origin`; push currently fails because GitHub DNS is unavailable. Do not force-push. Stop this packet on the named candidate value/use correspondence, a concrete source-owned construction obstruction, the time cap, or user STOP. R149, complete A/B proof, runtime and production remain OPEN.
