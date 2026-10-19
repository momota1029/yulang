# R109: finite nested-handler execution observation

Status: DRAFT_FOR_PRE_EXECUTION_REVIEW. Primary and sole integrator: Luna `/root`.
Parent: six independent effect-hygiene fronts, proof-backed method/role behavior,
and early runnable ordinary/effectful source execution. This sprint advances only
a finite ordered-handler/shallow-selection observation. It does not reduce the
other fronts or method/role obligations to this slice.

## Fixed observation

Use the existing, unmodified test
`tools/inference-playground/tests/runtime_handler_priority.rs`, test
`nested_handler_priority_and_shallow_arm_requests`, with exactly these three
cells and expected observations:

1. The exact source in the pinned test completes with integer `11`.
2. Swapping only the two inner Catch arms completes with integer `23`.
3. Changing only the outer arm pattern from `io::tick(p)` to `io::other(p)`
   yields an outward request for the source module's `tick` operation, integer
   payload `11`, and the inner arm's `io::tick 11` source range (`::tick 11`),
   distinct from the initial `io::tick 7` range.

The existing test bytes, source strings, expectations, test name and assertion
meaning are immutable inputs. No code, fixture, production source or expected
output may be edited. Preparation or execution mismatch is the recorded result;
no repair or retry is authorized.

## Authority and evidence ordering

R101 and R102 remain closed as `FAILED_TO_ACHIEVE_CONTRACT_PREREQUISITE`; their
commands were NOT_RUN. Their historical contracts and reviews are not reopened.
This new contract explicitly authorizes one finite public-API probe of the
existing test path, including shared source parsing/lowering, candidate solve,
`RuntimeProgram::from_hir`, start preparation, and the three machine runs. The
probe may establish that these exact three cells are runnable and satisfy their
assertions, or identify the first concrete obstruction.

This execution is evidence about these bytes and this test path. A pass does not
prove parser/CST constructor completeness independently of execution, does not
close historical `R101-ENTRY-1`, and does not establish universal handler
hygiene, arbitrary source correspondence, Simple-sub soundness/principality,
native residual correspondence, evaluator correctness, or adoption. The R101
conditional frame/receiving derivation may explain the predictions; it remains
conditional until the finite outcome observation and fresh reviews are recorded.
No test pass is promoted to a source-wide proof.

## Exact command and stop rule

After the frozen-input, pre-execution spec, proof and implementation reviews are
CLEAN, Luna alone may run exactly once:

```sh
CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test runtime_handler_priority nested_handler_priority_and_shallow_arm_requests -- --exact --nocapture
```

No alternate command, separate build, formatter, CLI, retry, or repair is
authorized. If the command starts, any compile/preparation/test failure consumes
the attempt. Preserve the complete command receipt and stop at the first failure
or mismatch. Maximum command wall time is 120 seconds.

## Frozen inputs

All direct inputs below were hashed at contract preparation. The change from the
R101 `program.rs` pin is limited to the `#[cfg(test)]` module added in commit
`0bd244f37`; production `RuntimeProgram` constructors used by this probe are
unchanged in that commit. A fresh compiler/source reviewer must verify this
boundary against the frozen old/new text and current relevant constructors.
The current file pin governs this observation; the old pin is preserved here to
make the version delta explicit.

| Input | SHA-256 |
|---|---|
| R101 rev2 contract `tasks/agent-loop/sprints/nested-handler-priority-20261019-r101-rev2.md` | `e8ba3e6280a3ee5d88881160de2bb8681b66c730a003e2c49e5c8bd94609946a` |
| R101 conditional proof `notes/theory/2026-10-19-r101-nested-handler-priority.md` | `d80b45e0188df46b089a287f9957eec67634213edd849c7165517c3892c09222` |
| R101 proof handoff `tasks/agent-loop/inbox/20261019-r101-proof.md` | `c544b911708480633c92d70c3e24bdcfcc1edfefdd95a8c00ff5f2a25a0ac0a6` |
| R101 implementation handoff `tasks/agent-loop/inbox/20261019-r101-implementation.md` | `45f6e77beaf43a0a7530e8cb9b8a5f859c547f3223f2b63237f0aa9078317cbb` |
| R101 closeout `notes/progress/2026-10-19-r101-nested-handler-priority.md` | `2b60c45691a30d66b858241edf838d0161f9c1d49df32054703024d4e04141e5` |
| Research charter `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| Ordinary-computation package `notes/design/2026-10-02-ordinary-computation-semantics-package.md` | `ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917` |
| R88 source bridge `notes/theory/2026-10-19-r88-ordered-selection-source-bridge.md` | `185eff03dfcef4cd9ea346434d60e34b39fcc0f34d46641b160decb58f0f1782` |
| R88 closeout `notes/progress/2026-10-19-r88-closeout.md` | `e190f71dc28010b59a8ccd973d42c7f146622b15cb59df87b96394a6de081bd9` |
| `tools/inference-playground/src/runtime/machine.rs` | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| `tools/inference-playground/src/runtime/receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| `tools/inference-playground/src/runtime/program.rs` current | `7bc27580711d3ef09044e324541904ef3388aca8e3b4f3a72437b1e04dc0210a` |
| `tools/inference-playground/src/runtime/program.rs` R101 historical | `484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11` |
| `tools/inference-playground/src/runtime/primitive.rs` | `97485b9439357497aaf3f19555b1d87eef4aabc955b3a2815f23cf49a65c0153` |
| `crates/yu-hir/src/module/local_source.rs` | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` |
| `tools/inference-playground/tests/runtime_receiving.rs` | `6ff65fc977c88837ec279b84088a6c2d89ebfc7f78915e7ac985904fcaa26bf2` |
| Existing test `tools/inference-playground/tests/runtime_handler_priority.rs` | `cdcb06ceebcca48cd3ff6fbc1a429243e9013a148c5fc895d9926e5dc2ce07db` |

Any other input drift or need for a new source owner stops dependent work pending
a versioned contract update and fresh review. Do not infer provenance or
constructor behavior from a historical hash.

## Leases and outputs

- Proof lane: `notes/theory/2026-10-19-r109-nested-handler-observation.md` and
  `tasks/agent-loop/inbox/20261019-r109-proof.md`. Reuse the conditional R101
  transition derivation only where the current pins still support it; state the
  finite observation protocol, concrete result after execution, and all open
  boundaries. No new theorem or semantic rule.
- Implementation lane is read-only over the pinned existing test and relevant
  source. Sole output: `tasks/agent-loop/inbox/20261019-r109-implementation.md`,
  recording exact cells/assertions and byte stability. No code lease.
- Fresh pre-execution spec reviewer: this contract and every listed pin; check
  evidence ordering, exact test/command, no expected-output relaxation, and
  that the finite probe has explicit authority without closing static or
  universal gates.
- Fresh post-output spec reviewer: frozen producer outputs and same pins; check
  results and claim boundaries.
- Independent compiler/source reviewer: current pinned `machine.rs`,
  `receiving.rs`, `program.rs`, `primitive.rs`, `local_source.rs`, test and R101
  proof. Check exact current constructor path, request identity/source lineage,
  receiving/handler transition, the test-only program delta, and type/source
  plausibility. Reviewers do not execute the command.
- Luna owns state, command, review adjudication, closeout, explicit-path Git
  integration and push. Producers stop after output freeze.

All lane inspection is read-only and limited to the exact frozen inputs and
leased outputs. No lane may run a test/build/compiler/runtime/formatter/CLI/Git
command. Preserve three inherited UNKNOWN identities, board quarantine,
historical R104 lease and legacy slot reservation. Admit no more than two
producers concurrently; do not reclaim an unknown lease.

## Resource ceiling and stop

Total ceiling: 1,200 seconds: proof 360, implementation inventory 180,
pre/post spec reviews combined 120, compiler/source review 180, command 120,
Luna integration/closeout 240. Astra 0. Individual stage allowances do not
increase the total. Stop on any pin mismatch, unreviewed source owner, major or
blocking review finding, command failure, output mismatch, provenance mismatch,
or budget exhaustion. Preserve all earlier R101/R102/R106/R107 results.

This finite slice advances one of the six hygiene fronts and early executable
source evidence. It creates no production authority, no R85 adoption and no
closure for the other effect fronts, method/role proofs, Simple-sub claims or
evaluator claims. Next sprint selection must rotate to another open front or
method/role/source execution rather than repeat this already observed fixture.
