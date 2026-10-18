# r11 — typed slot-42 observation and one-shot source/native probe

Status: **ACTIVE**, frozen by Luna after all 15 direct dependency hashes matched.
Sprint: `npair-operation-frontier-typed-slot-observation-20261018-r11`.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, still **OPEN / closure 0**.
Baseline HEAD: `fdaeebf89bf74cf6eaedb85ced0cbe497f31c37c`. The only working-tree code delta is the r10 test-only candidate at `candidate_effect.rs`; its exact baseline hash is pinned below.

## Original outcome and limits

Original fixed `c`, quantifiers, source domain, R/W/Z, `rho_u`, consumer, F1/FK1 and accepted semantics remain unchanged. The authentic historical source/CST/HIR and complete semantic Operation package remain `INPUT_UNAVAILABLE` (r10 input receipt). This packet makes no theorem claim and cannot close any original condition.

The bounded goal is to make the existing test-only probe compile by checking slot-42 publication through the existing typed provenance owner: `ConstraintStore::provenance()` and `ProvenanceEdge::cause().occurrence()`. `SemanticFact::id()` is an opaque `FactId`; it is not a source occurrence. This adapts the assertion to the existing owner evidence, without changing expected solver behavior or production semantics.

Success evidence, in order:

1. Fresh independent review CLEAN on the exact one-line observation repair and handoff.
2. One exact offline compile-only command succeeds and yields the executable path.
3. After rehashing all pinned source inputs and the executable immediately before launch, exactly one direct invocation of the full exact test path succeeds and captures complete logs/meta.
4. A separate fresh receipt reviewer confirms source/use identity, Action::Operation boundary, prefix-preserving root cleanup, provenance-based slot42 non-publication, and invocation hashes. This proves only bounded behavior of the new research rendering. The inner negative-row guard remains static attribution.

A compile/test failure ends this grant. No retry, changed expectation, semantic repair or historical-source claim. Do not assert whole-parent rollback; successful prefix facts remain. Do not alter existing fixtures/assertions beyond the new test's typed slot-42 check.

## Continuing lanes

- **Proof:** WAITING for changed semantic input. The exact original Operation package is still unavailable; generic reproof over the same uninstantiated interface is not useful. Luna remains owner of recovering literal original source/HIR, fixed `F_c`, complete `Sigma.Lambda`, output/license and consumer. F1/FK1 and the original parent stay open.
- **Implementation:** Luna/high owns only `crates/yu-solver/src/candidate_effect.rs` (the existing named test) and `tasks/agent-loop/inbox/20261018-npair-operation-frontier-r11-impl.md`.
- **Review:** fresh independent `compiler_referee` on exact source+handoff before any build. A fresh `spec_auditor`/runtime receipt reviewer checks logs after the one invocation.
- **Astra:** 0. One heavyweight Cargo process maximum. No parallel build.

## Exact dependency manifest

All files are read-only except the two implementation outputs above, current state owned by Luna, and three runtime outputs owned by Luna after the review gate.

| Path | SHA-256 |
|---|---|
| `Cargo.toml` | `d61446115ce45d7010898090bce323fe1134b1cca53471ac9416e441d45865d9` |
| `Cargo.lock` | `2055b82e7c2c68df727940d7053da0490368a99217bd3587866a7003177484e6` |
| `crates/yu-solver/Cargo.toml` | `7a599e95800c67ca4688b0f91917609345a252aae6d2ea6cd0f413eb1c07893c` |
| `crates/yu-solver/src/candidate_effect.rs` | `22a9e7a25f59638a24df746be9954ec711ca99f7c89802fa75808d7e07fdcca3` |
| `crates/yu-solver/src/candidate_source.rs` | `1a65c7afb02a4afd538a34c34086108959579e06aafe8fbcab8ad6a6b3a65f3e` |
| `crates/yu-solver/src/lib.rs` | `ddd1395877d4a76e27a1dcf32af90c6fcb0e58c739610a0115c03955628350e1` |
| `crates/yu-solver/src/candidate_context_tests.rs` | `45465871d4eec1dea86bb7fa652a253b82e293ce91512608df6c06ab248eec95` |
| `crates/yu-hir/src/module/source_annotation.rs` | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| `crates/yu-hir/src/module/local_source.rs` | `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5` |
| `crates/yu-solver/src/shadow_apply.rs` | `eb0b9dcd8529e067ec8778c7888f3595ad8df466e1be4243b1d2104c853952d7` |
| `notes/theory/2026-10-17-choose-operation-source-instantiation.md` | `6075d45f38787bd5a981a2da177504450239a05e6dbec6f19ccf526ca0d4a110` |
| `tasks/agent-loop/inbox/20261018-npair-original-term-input-r10.md` | `f4ea6658d4f097b74b04af0479dc61659fd361a6099777eb5044ebae37223175` |
| `tasks/agent-loop/sprints/npair-original-input-and-operation-frontier-20261018-r10-closeout.md` | `7fe46fe2dce6ab07b4d4806dfe2c204242f60944d63598c060a7415d21894899` |
| `tasks/agent-loop/runtime/20261018-operation-frontier-r10.meta.json` | `153d47ebfaf5193fb0ac6390117ce592639ce90ca7b2b67a4a8b7004c886cdc1` |
| `tasks/agent-loop/runtime/20261018-operation-frontier-r10.stderr.log` | `2fc1c799b171db1ce8c58d62c06ddba5a31418e7fa570f9007cbf83f9d4e8fae` |

The `candidate_effect.rs` pin is the exact r10 test input, not a clean HEAD blob. The prior compile failure and review receipts remain historical and are not reclassified. Any mismatch before write or test cancels this exact packet.

## One-shot verification and capture

After fresh CLEAN review, run exactly once:

```sh
cargo test --offline -p yu-solver --features shadow-apply-candidate --lib --no-run candidate_effect::tests::original_choose_operation_rendering_reaches_native_frontier
```

Retain Cargo's printed executable path. If build succeeds, immediately rehash every input in the table (target now at the reviewed r11 SHA) and the executable. Then invoke that executable directly once with:

```text
candidate_effect::tests::original_choose_operation_rendering_reaches_native_frontier --exact --nocapture
```

Capture complete stdout/stderr directly to:

- `tasks/agent-loop/runtime/20261018-operation-frontier-r11.stdout.log`
- `tasks/agent-loop/runtime/20261018-operation-frontier-r11.stderr.log`
- `tasks/agent-loop/runtime/20261018-operation-frontier-r11.meta.json`

Metadata must record UTC start/end, monotonic duration, actual executable path and argv, exit code, all target source/dependency SHA-256 values at invocation, executable SHA-256 at invocation and log hashes. Do not reconstruct missing evidence. If compile fails, record no direct invocation and stop.

## Resources, integration and stop conditions

Fresh successor cap **720 seconds**, no rollover: Luna repair/handoff120, fresh independent code review180, one compile+direct exact test120, independent receipt review180, Luna integration/state/Git120. Astra0; one heavyweight Cargo process. The previous r10 budget is closed, not transferred.

After review/receipt, Luna updates compact state and a short closeout. Commit/push only the reviewed research result and runtime receipt; test instrumentation stays test-only and does not authorize production behavior. Inspect the full outbound range first; never force-push. Stop on pin mismatch, first compile/test failure, unrelated source edits, semantic dependency, missing instrumentation owner, budget limit, or unconfirmed writer.
