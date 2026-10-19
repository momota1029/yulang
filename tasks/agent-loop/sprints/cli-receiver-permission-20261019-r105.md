# R105: expose the finite sibling-receiver contrast through CLI

Status: DRAFT, revision 1. Primary: Luna `/root`. This follows R104's source-identity stop. R104 artifacts are excluded. R105 reuses R96's independently reviewed wrong/sibling permission pair and checks the public stdin CLI with those exact source bytes.

## Fixed finite outcome

Use exactly the two R96 UTF-8 source strings, passed to the child process via stdin. Both strings have **no final LF**.

P, 210 bytes, SHA-256 `765a89c4cee89ceaf4213663b1be8e3110d0f81f4026d2112ddf4ee2f9a23780`:

```yu
act io:
    our tick: int -> int
    our other: int -> int
my relay (thunk:[io] int) = {
    my helper (pending:[io] int) = catch pending { io::tick(p), _ -> p }
    helper(thunk)
}
my main = relay (io::tick 7)
```

N changes exactly `catch pending` to `catch thunk`, 208 bytes, SHA-256 `e1b42dbbbd1141c35857a552123e78f4bb8fe69d55bdd2429aaa6614f135705c`. No other byte changes.

Add one serial subprocess integration test named `receiver_permission_controls_cli_publication` at `tools/inference-playground/tests/cli_receiver_permission.rs`. For each exact byte string, launch `CARGO_BIN_EXE_yu-playground` with `--run main --steps 10000 -`, write the bytes to stdin with no appended newline, then check process status and streams.

Expected finite observations:

- P: exit success, stdout exactly `7\n`, stderr empty.
- N: exit failure, stdout empty, stderr contains the existing `runtime unavailable: HandlerEvidence` diagnostic.

R96 observed the same source bytes through the runtime integration test: P completes with `7`; N returns candidate `RuntimeUnavailable::HandlerEvidence`. R105 tests the new stdin module identity and public publication. Source IDs across the R96 and R105 `FileKey`s are independently branded; do not equate their numeric identities or claim general source-name independence. The negative outcome is candidate implementation behavior, not a language rejection rule or a general sibling-protection theorem.

This does not establish native K,D or residual correspondence, general permission soundness, unmatched suffix preservation, broad §21 behavior, source-wide CLI soundness, method/role dispatch, Simple-sub/evaluator parent closure, semantic adoption, or production authority.

## Leases and authority

Proof lane owns only:

- `notes/theory/2026-10-19-r105-cli-receiver-permission.md`
- `tasks/agent-loop/inbox/20261019-r105-proof.md`

Implementation lane owns only:

- `tools/inference-playground/tests/cli_receiver_permission.rs`
- `tasks/agent-loop/inbox/20261019-r105-implementation.md`

All other inputs are read-only. No production edits or fixture changes. No worker may run tests/build/CLI/runtime/formatter/Git. A newly required owner or source identity mismatch is a stop requiring a new reviewed contract.

## Frozen inputs

| Input | SHA-256 |
|---|---|
| R96 contract `tasks/agent-loop/sprints/sibling-receiver-permission-20261019-r96.md` | `195468ceef7c5fe29aee157260e9f0c218a5dd3e95ed759c40f1f86b348d4892` |
| R96 proof `notes/theory/2026-10-19-r96-sibling-receiver-permission.md` | `2e6026e77d04fa6385e82ecf62cf9f0e63448bcd7619fb6500f11ca2789fe9a9` |
| R96 closeout `notes/progress/2026-10-19-r96-sibling-receiver-permission.md` | `f106525812de5a2788b465dfffb4d8a386883aa8d90b631616ea4bdcb5dd9533` |
| R96 proof handoff `tasks/agent-loop/inbox/20261019-r96-proof.md` | `84b3302c61e4a20e882552c960c95dadb5e9cb14bae80a5e9e810815f18de583` |
| R96 implementation handoff `tasks/agent-loop/inbox/20261019-r96-implementation.md` | `fb99947f978ab905bc65e5f7291ff38f18a74c062b2bc1fe2c5f85113f69b2d6` |
| R96 spec review `tasks/agent-loop/inbox/20261019-r96-spec-review.md` | `c43298fcea613e065bd41cceddddaf4c921d060c3cb47263f027acdecb780294` |
| R96 compiler review `tasks/agent-loop/inbox/20261019-r96-compiler-review.md` | `7390302bd1055ea95f4b73cc20d7a2e356199a915882885e4db422be56b50cdc` |
| R96 exact positive/negative runtime case `tools/inference-playground/tests/runtime_receiving.rs` | `6ff65fc977c88837ec279b84088a6c2d89ebfc7f78915e7ac985904fcaa26bf2` |
| CLI argument, stdin identity and publication `tools/inference-playground/src/main.rs` | `75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100` |
| Source preparation, runtime invocation and outcome mapping `tools/inference-playground/src/lib.rs` | `bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b` |
| Bounded output/error publication `tools/inference-playground/src/output.rs` | `04e99c5bdb562a8edb8a7e17bdcc03f7b46eaca9d8e13b20216b4dcf3032a88a` |
| Runtime source schedule and outcomes `tools/inference-playground/src/runtime/machine.rs` | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| Runtime Lambda/handler preparation `tools/inference-playground/src/runtime/program.rs` | `7bc27580711d3ef09044e324541904ef3388aca8e3b4f3a72437b1e04dc0210a` |
| Receiver permission and HandlerEvidence boundary `tools/inference-playground/src/runtime/receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| Existing public CLI subprocess convention `tools/inference-playground/tests/cli.rs` | `cf265feba7414b159353c81751608e9c127b072559b2c8c4cc513ecbc15c22ea` |
| Test target/package `tools/inference-playground/Cargo.toml` | `87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56` |

No R104 artifact is an R105 dependency.

## One Luna-owned verification command

After proof and implementation freeze and fresh independent post-output spec/compiler-source reviews are CLEAN, Luna may run exactly once:

```sh
CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test cli_receiver_permission -- --exact receiver_permission_controls_cli_publication --nocapture
```

No retry or alternate command is authorized. Failure, timeout, source drift, unexpected stdout/stderr or status closes R105 without repair.

## Resources and stop conditions

- Proof: Sol/high, cap 600 seconds.
- Test-only implementation: Luna/high, cap 360 seconds.
- Fresh pre/post spec reviews: 180 seconds total.
- Compiler/source review: 240 seconds.
- One Luna-owned command: 120 seconds maximum.
- Integration/closeout: 300 seconds.
- Total cap: 1,800 seconds; Astra 0.

Preserve UNKNOWN identities, board quarantine and reserved legacy slot; at most two producers. Stop on missing owner, source identity mismatch, review blocker/major, command failure, budget exhaustion or unknown writer.

## Breadth boundary

This is one wrong/sibling permission contrast joined to the runnable effectful CLI. It leaves the other five hygiene fronts, method/role proof, ordinary/effectful source breadth, original Simple-sub/evaluator quantifiers and semantic adoption independent and open. Do not turn this finite candidate result into a language rule or let storage/fiber work dominate later selection.
