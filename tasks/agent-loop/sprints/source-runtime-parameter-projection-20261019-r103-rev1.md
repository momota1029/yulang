# R103: source-to-runtime parameter projection

Status: DRAFT, revision 1. Primary: Luna `/root`. This packet follows the R102 missing-owner stop by rotating to a distinct static-to-runtime projection obligation already supported by R97 evidence.

## Fixed finite outcome

Show that runtime Lambda emission preserves the original LocalSource formal and its annotation role/owner when constructing both the runtime `ParameterRole` and a positive `RootCompSchema`. Use the exact R97 C-loop source cell, whose candidate preparation and runtime completion were already observed in R97:

```yu
act signal:
    our ping: () -> int
my loop x = loop x
my ignore (x:[] int) = 9
my main = ignore (loop ())
```

The new test is a test-only unit test inside `tools/inference-playground/src/runtime/program.rs`. From the exact source, lower to authentic `LocalSource`, call `RuntimeProgram::from_hir`, find the original `ignore` Lambda by its LocalSource occurrence, and compare:

- the original `LocalSourceParameter` ID and retained annotation owner/key/type/effect-row presence;
- the emitted `Instruction::Lambda` formal ID and `ParameterRole::Computation`;
- the emitted `RootCompSchema.formal` and Lambda `SourceSite` root/occurrence;
- the original unannotated `loop` formal's `ParameterRole::Value` and absent schema as a finite negative control.

Keep the exact existing R97 runtime integration result (`9`) as the observed invocation outcome. The new test checks the source-to-program projection independently; it does not replace that integration observation or use a simulated instruction. This is a finite constructor lemma only. It does not establish source-wide static-to-runtime soundness, candidate-to-runtime permission equivalence, method/role dispatch, continuation or residual correspondence, Simple-sub/evaluator parent closure, semantic adoption, or production authority.

## Leases and exact outputs

Proof lane owns only:

- `notes/theory/2026-10-19-r103-parameter-projection.md`
- `tasks/agent-loop/inbox/20261019-r103-proof.md`

Implementation lane owns only:

- `tools/inference-playground/src/runtime/program.rs` (test-only addition under `#[cfg(test)]`; no production behavior edits)
- `tasks/agent-loop/inbox/20261019-r103-implementation.md`

All other inputs are read-only. Workers may use bounded text/hash inspection against only the exact pins and their leased output files. No worker may execute tests, builds, compiler/runtime, formatter, CLI or Git. Any required owner outside the pin set is an exact stop; no ad hoc dependency expansion.

## Frozen inputs

| Input | SHA-256 |
|---|---|
| R97 contract `tasks/agent-loop/sprints/value-computation-entry-20261019-r97.md` | `2a9e65fd973e4d9c7f0916440fe8438eb6e9a8b8cd7969dc8f89025d9cf1b1ce` |
| R97 proof `notes/theory/2026-10-19-r97-value-computation-entry.md` | `77b4ea777a2fd413b356b5128cc55362f1126e6298bcb7c310f776cfd53b4b98` |
| R97 closeout `notes/progress/2026-10-19-r97-value-computation-entry.md` | `aa06b04ff9ad0fb882c89c26e0375fd21eddba489c44b7d54f6156585a66d734` |
| R97 proof handoff `tasks/agent-loop/inbox/20261019-r97-proof.md` | `6a84958c082f6ec9575cb13962ad395c4246a5e7636df6921429399503eabdfb` |
| R97 implementation handoff `tasks/agent-loop/inbox/20261019-r97-implementation.md` | `b6d9b8206ca433839ab48b9822f8546bf89d40099a2e8e763da1cb6d210ec39d` |
| R97 integration test `tools/inference-playground/tests/runtime_control.rs` | `2619e4c8bb006e2d98cf81887091ae372cb1ae3731de76e7b707a97db577009c` |
| `crates/yu-syntax/src/lib.rs` | `18709b87b1b761374b5b81f90fcbf37d001fd7d981597e889aef05ad3f230f93` |
| `crates/yu-syntax/src/full_parse.rs` | `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8` |
| `crates/yu-syntax/src/declaration/binding.rs` | `eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544` |
| `crates/yu-syntax/src/pattern/mod.rs` | `1b608422c93ce0f6947125a9b1ea88314a48b3a5e45030ed23e5154492ad7883` |
| `crates/yu-syntax/src/type_expr/mod.rs` | `2e08a49960cd4010ba39641ae509afb7cf59711c1464d3349f5f6db590ebf01f` |
| `crates/yu-syntax/src/type_expr/variants.rs` | `8ccf273de0d475b999207f216822f35354cdee51a2b00aba3a8be5bafd2bc16e` |
| `crates/yu-hir/src/lib.rs` | `8f6e2b688418dbdb4e2c551cbd9b7b58c809623d492f2da6f7d29cc64189d8d8` |
| `crates/yu-hir/src/source_identity.rs` | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |
| `crates/yu-hir/src/shadow.rs` | `9f7a80055076a01cbd99a3eb9c5bc8c3f0db512f2e84032a53af0eacdad2375b` |
| `crates/yu-hir/src/module.rs` | `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a` |
| `crates/yu-hir/src/module/local_source.rs` | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` |
| `crates/yu-hir/src/module/source_annotation.rs` | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| `tools/inference-playground/src/runtime/program.rs` (pre-edit) | `484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11` |
| `tools/inference-playground/src/runtime/receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| `tools/inference-playground/src/runtime/primitive.rs` | `97485b9439357497aaf3f19555b1d87eef4aabc955b3a2815f23cf49a65c0153` |

R97's exact prior command/result are borrowed only for the exact C-loop integration cell. R97 did not inspect or produce this new unit test. A required new source owner stops R103 before edits and requires a revised contract.

## One Luna-owned verification command

After both lane outputs freeze and fresh independent spec/compiler reviews are CLEAN, Luna may run exactly once:

```sh
CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --lib runtime::program::tests::runtime_program_emits_computation_role_with_original_formal_and_schema -- --exact --nocapture
```

No retry, alternate command, build-only command, formatter or CLI is authorized. A command failure or assertion mismatch ends R103 without repair. A passing unit test establishes only the emitted role/schema to original-formal correspondence for this exact R97 source cell; it is not a second integration run or a parent theorem.

## Resources and stop conditions

- Proof: Sol/high, cap 600 seconds.
- Test-only implementation: Luna/high, cap 360 seconds.
- Fresh pre/post spec review: 180 seconds total.
- Independent compiler/source review: 240 seconds.
- One Luna-owned command: 120 seconds max.
- Integration and closeout: 300 seconds.
- Total cap: 1,800 seconds; Astra 0.

Preserve all UNKNOWN identities, board quarantine and reserved legacy slot; at most two producers. Stop on missing owner, source identity mismatch, lost empty-row marker, changed formal, role/schema mismatch, review blocker/major, command failure, budget exhaustion or unknown writer. No production behavior change, language semantic adoption, method/role promotion or inference rule change is authorized.

## Breadth boundary

This advances one finite static-to-runtime projection slice, not the entire front. After closeout, select the next bounded outcome across the other effect-hygiene fronts, method/role proofs, and early ordinary/effectful source execution. Storage/fiber work does not monopolize the sequence.
