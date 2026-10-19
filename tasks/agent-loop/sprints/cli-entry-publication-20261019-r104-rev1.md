# R104: publish finite runtime outcomes through the public CLI

Status: DRAFT, revision 1. Primary: Luna `/root`. This follows closed R103 and the sprint-end selector's recommendation to join an already reviewed finite source cell to the runnable `--run` surface. It advances the unmatched outward-request consumer and early source execution without extending R101's parser boundary.

## Fixed finite outcome

Use exactly the two source cells already present in R97's pinned `runtime_control.rs` §21 test:

```yu
act signal:
    our ping: () -> int
my ignore x = 9
my main = ignore (signal::ping())
```

```yu
act signal:
    our ping: () -> int
my ignore (x:[] int) = 9
my main = ignore (signal::ping())
```

Add these as `tools/inference-playground/examples/entry-unmatched-request.yu` and `tools/inference-playground/examples/entry-computation-argument.yu`, preserving the exact source bytes above. Add one integration test at `tools/inference-playground/tests/cli_entry_publication.rs` that runs the public `yu-playground --run main --steps 1000 <example-path>` binary serially for each source.

Expected finite outcomes:

1. The Value-role formal evaluates the argument first, the request is unmatched, and the CLI exits unsuccessfully with empty stdout and the existing `unhandled runtime request` diagnostic on stderr. No completed result is published.
2. The `[] int` Computation-role formal receives the request computation without running it; the ignored argument permits the body to complete. The CLI exits successfully with stdout exactly `9\n` and empty stderr.

The test must check exit status, exact stdout, and the relevant stderr condition for both runs. This is a public-consumer observation for these two source cells. It does not prove unmatched suffix preservation, general §21 behavior, source/native permission equivalence, handler/continuation behavior, source-wide CLI soundness, method/role dispatch, Simple-sub/evaluator parent closure, semantic adoption, or production authority. R97's prior runtime_control integration receipt is reused only for these exact cells and expectations; R104 newly observes publication through the CLI.

## Exact leases and authority

Proof lane owns only:

- `notes/theory/2026-10-19-r104-cli-entry-publication.md`
- `tasks/agent-loop/inbox/20261019-r104-proof.md`

Implementation lane owns only:

- `tools/inference-playground/examples/entry-unmatched-request.yu`
- `tools/inference-playground/examples/entry-computation-argument.yu`
- `tools/inference-playground/tests/cli_entry_publication.rs`
- `tasks/agent-loop/inbox/20261019-r104-implementation.md`

All other inputs are read-only. No production changes or fixture expectation edits. No worker may run tests, build, compiler/runtime CLI, formatter or Git. Missing owners require a stop and a revised, freshly reviewed contract.

## Frozen inputs

| Input | SHA-256 |
|---|---|
| R97 contract `tasks/agent-loop/sprints/value-computation-entry-20261019-r97.md` | `2a9e65fd973e4d9c7f0916440fe8438eb6e9a8b8cd7969dc8f89025d9cf1b1ce` |
| R97 proof `notes/theory/2026-10-19-r97-value-computation-entry.md` | `77b4ea777a2fd413b356b5128cc55362f1126e6298bcb7c310f776cfd53b4b98` |
| R97 closeout `notes/progress/2026-10-19-r97-value-computation-entry.md` | `aa06b04ff9ad0fb882c89c26e0375fd21eddba489c44b7d54f6156585a66d734` |
| R97 proof handoff `tasks/agent-loop/inbox/20261019-r97-proof.md` | `6a84958c082f6ec9575cb13962ad395c4246a5e7636df6921429399503eabdfb` |
| R97 implementation handoff `tasks/agent-loop/inbox/20261019-r97-implementation.md` | `b6d9b8206ca433839ab48b9822f8546bf89d40099a2e8e763da1cb6d210ec39d` |
| R97 exact source/test owner `tools/inference-playground/tests/runtime_control.rs` | `2619e4c8bb006e2d98cf81887091ae372cb1ae3731de76e7b707a97db577009c` |
| Public argument and outcome mapping `tools/inference-playground/src/lib.rs` | `bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b` |
| Public CLI argument/stdout/stderr/exit mapping `tools/inference-playground/src/main.rs` | `75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100` |
| Runtime source schedule and outcome constructors `tools/inference-playground/src/runtime/machine.rs` | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| Lambda role and computation schema emission `tools/inference-playground/src/runtime/program.rs` | `7bc27580711d3ef09044e324541904ef3388aca8e3b4f3a72437b1e04dc0210a` |
| Computation receiving certificate `tools/inference-playground/src/runtime/receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| Existing subprocess integration-test convention `tools/inference-playground/tests/cli.rs` | `cf265feba7414b159353c81751608e9c127b072559b2c8c4cc513ecbc15c22ea` |
| Cargo target name `tools/inference-playground/Cargo.toml` | `87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56` |

A new source owner required for either exact trace or test harness is a stop. No pin may be silently expanded.

## One Luna-owned verification command

After both producer outputs freeze and fresh independent specification and compiler/source reviews are CLEAN, Luna may run exactly once:

```sh
CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test cli_entry_publication -- --exact entry_role_controls_cli_publication --nocapture
```

No retries, alternate commands, build-only commands, formatters, or direct CLI invocations are authorized. Any mismatch or command failure closes R104 as FAILED_TO_ACHIEVE with no repair in this sprint.

## Resources and stop conditions

- Proof: Sol/high, cap 600 seconds.
- Test/examples: Luna/high, cap 360 seconds.
- Fresh pre/post spec review: 180 seconds total.
- Independent compiler/source review: 240 seconds.
- One Luna-owned command: 120 seconds maximum.
- Integration/closeout: 300 seconds.
- Total cap: 1,800 seconds; Astra 0.

Preserve all UNKNOWN identities, the board quarantine, and reserved legacy slot; at most two producers. Stop on missing source owner, source identity mismatch, either output expectation mismatch, review blocker/major, command failure, budget exhaustion, or unknown writer. The public CLI result is not a production guarantee or parent theorem.

## Breadth boundary

This slice observes unmatched request publication and a normally completed effectful source through the public CLI. It does not close the unmatched-suffix, handler-priority, sibling-permission, continuation/resumption, whole projection, or source-wide entry fronts. Keep method/role proofs and their adoption gate active in subsequent sprint selection. Do not let storage/fiber work monopolize the sequence.
