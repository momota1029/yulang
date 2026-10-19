# R110: §21 entry demand through source execution and CLI publication

Status: DRAFT_FOR_PRE_EXECUTION_REVIEW. Primary and sole Git integrator: Luna
`/root`. Parent goal: broad, deep progress across six separate effect-hygiene
fronts, proof-backed method/role behavior, and early runnable ordinary/effectful
source execution. This sprint advances the finite §21 Value/Computation entry
front using an ordinary recursive source and the public stdin CLI.

## Fixed finite source pair

Use the exact `DECL` prefix and two R97 ordinary-call bodies below. Concatenate
the prefix with each body exactly; neither complete string has a final LF.

```text
DECL = "act signal:\n    our ping: () -> int\n"
```

Value cell, 97 UTF-8 bytes, SHA-256
`1c1d1d5d98c1acc3148f199408cb1324a4c1fee3aa4474034ed7495d7ee54446`:

```text
my loop x = loop x
my ignore x = 9
my main = ignore (loop ())
```

Computation cell, 106 UTF-8 bytes, SHA-256
`ac926feeb27c26d81f8545ac05810dbcf7f8dd60719b84fee316db2417b8ec73`:

```text
my loop x = loop x
my ignore (x:[] int) = 9
my main = ignore (loop ())
```

Test them serially from one integration test,
`entry_demand_controls_cli_completion`, in
`tools/inference-playground/tests/cli_entry_demand.rs`. Each child uses stdin
and these exact arguments: `--run main --steps 10000 -`.

Fixed expected observations:

1. The Value formal `ignore x` repeatedly demands the recursive `loop ()`
   argument. At the finite 10,000-step budget, the CLI exits unsuccessfully,
   publishes no stdout, and reports the existing step-budget-exhausted
   diagnostic on stderr.
2. The Computation formal `ignore (x:[] int)` binds the whole argument as an
   inert computation and returns its body value. The CLI exits successfully,
   stdout is exactly `9\n`, and stderr is empty.

These observations concern two exact inputs and finite fuel. Exhausting 10,000
steps is not a proof of mathematical divergence. Do not claim that every Value
argument is eager in general, that every Computation argument is safe, or that
the public CLI is source-wide sound.

## Authority, evidence and stop rules

R97's six-cell test and closeout establish a finite candidate/runtime contrast;
R103's exact C-loop projection and R105's subprocess convention are reusable
only within their stated domains. R110 adds a public stdin subprocess
observation for these two exact bytes. A green command connects their source
execution to exit/stdout/stderr outcomes; it does not prove a universal §21
theorem, full source constructor completeness, divergence, effect hygiene,
Simple-sub/evaluator correctness, method typing/lookup/dispatch, R85 adoption,
or production authority.

R109 ended with a separate source-range mismatch in a nested handler fixture.
That fixture, test and range expectation are not inputs to R110 and must not be
reused, edited or diagnosed here.

Implementation may add only the one leased integration test and its handoff.
No production source, examples, CLI behavior, expected baseline tests or
preexisting files may be edited. A source mismatch, preparation failure,
wrong exit/output, or unexpected diagnostic is a stop; no repair/retry.

## Exact command

After all producer outputs are frozen and fresh post-output spec and
compiler/source reviews are CLEAN, Luna alone may run exactly once:

```sh
CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test cli_entry_demand entry_demand_controls_cli_completion -- --exact --nocapture
```

No alternate command, separate build, formatter, CLI invocation outside this
test, retry or repair is authorized. A command start consumes the one attempt,
even on compile or setup failure. Preserve the command result and stop.

## Frozen inputs

All hashes below were checked at contract preparation.

| Input | SHA-256 |
|---|---|
| R97 contract `tasks/agent-loop/sprints/value-computation-entry-20261019-r97.md` | `2a9e65fd973e4d9c7f0916440fe8438eb6e9a8b8cd7969dc8f89025d9cf1b1ce` |
| R97 conditional proof `notes/theory/2026-10-19-r97-value-computation-entry.md` | `77b4ea777a2fd413b356b5128cc55362f1126e6298bcb7c310f776cfd53b4b98` |
| R97 proof handoff `tasks/agent-loop/inbox/20261019-r97-proof.md` | `6a84958c082f6ec9575cb13962ad395c4246a5e7636df6921429399503eabdfb` |
| R97 implementation handoff `tasks/agent-loop/inbox/20261019-r97-implementation.md` | `b6d9b8206ca433839ab48b9822f8546bf89d40099a2e8e763da1cb6d210ec39d` |
| R97 closeout `notes/progress/2026-10-19-r97-value-computation-entry.md` | `aa06b04ff9ad0fb882c89c26e0375fd21eddba489c44b7d54f6156585a66d734` |
| R97 exact integration input `tools/inference-playground/tests/runtime_control.rs` | `2619e4c8bb006e2d98cf81887091ae372cb1ae3731de76e7b707a97db577009c` |
| R103 projection proof `notes/theory/2026-10-19-r103-parameter-projection.md` | `114f5bcfa31a50ffc6111364f28d1e0f1abe41d94030dc1a5afc3d4e66756c74` |
| R103 proof handoff `tasks/agent-loop/inbox/20261019-r103-proof.md` | `c2cf5b99d0948a016792b62199ada85b87ee2f7d18a93dc66d2d6e11bb0abe0d` |
| R103 implementation handoff `tasks/agent-loop/inbox/20261019-r103-implementation.md` | `5fe82c14d4fe0c248699206235ebdf689f79f67939b53ad2c8936e460b1a69ed` |
| R103 closeout `notes/progress/2026-10-19-r103-parameter-projection.md` | `701abe0a6f319eab8c282281ff66f66a63a8758becd238b44d30581894d49377` |
| R105 contract `tasks/agent-loop/sprints/cli-receiver-permission-20261019-r105.md` | `2e037e3848b95f7a60f5809e4a88018b7088d12489cb45149fceca38ed3f1d77` |
| R105 closeout `notes/progress/2026-10-19-r105-cli-receiver-permission.md` | `8b1662794800df84b65839c27d3536ed7b05068e6c74955ed44f6b86377b7a07` |
| R105 implementation handoff `tasks/agent-loop/inbox/20261019-r105-implementation.md` | `f92e6b9ab118f14e4a43d97bf03b7d0d8fc39dbddf6404a1f3849d763859cca8` |
| CLI entry-publication test `tools/inference-playground/tests/cli_entry_publication.rs` | `ac2ba1cb201f35c79dbc67d140012b2c5db4b43c2395efe804be7e9a11f9535e` |
| CLI args/stdin route `tools/inference-playground/src/main.rs` | `75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100` |
| Source preparation/runtime/output API `tools/inference-playground/src/lib.rs` | `bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b` |
| Bounded output `tools/inference-playground/src/output.rs` | `04e99c5bdb562a8edb8a7e17bdcc03f7b46eaca9d8e13b20216b4dcf3032a88a` |
| Runtime machine `tools/inference-playground/src/runtime/machine.rs` | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| Runtime program `tools/inference-playground/src/runtime/program.rs` | `7bc27580711d3ef09044e324541904ef3388aca8e3b4f3a72437b1e04dc0210a` |
| Receiving schema/entry `tools/inference-playground/src/runtime/receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| Existing subprocess pattern `tools/inference-playground/tests/cli.rs` | `cf265feba7414b159353c81751608e9c127b072559b2c8c4cc513ecbc15c22ea` |
| Package/test target `tools/inference-playground/Cargo.toml` | `87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56` |

Any pin mismatch or newly required source owner stops the packet pending a
versioned contract and fresh review. All inspection is limited to this exact
dependency set and leased outputs.

## Leases, review and resources

- Proof lane owns only `notes/theory/2026-10-19-r110-cli-entry-demand.md` and
  `tasks/agent-loop/inbox/20261019-r110-proof.md`. Derive finite Value versus
  Computation entry under R97's authentic source/receiver conditions, connect
  the tested subprocess boundary, preserve finite-fuel limits and leave all
  universal/adoption claims open.
- Implementation lane owns only
  `tools/inference-playground/tests/cli_entry_demand.rs` and
  `tasks/agent-loop/inbox/20261019-r110-implementation.md`. Use exactly two
  serial child processes and exact stdin bytes, args, statuses and streams.
- Fresh pre-edit spec review owns
  `tasks/agent-loop/inbox/20261019-r110-pre-spec-review.md`.
- Fresh post-output spec and compiler/source reviewers are read-only; Luna
  records their returned receipts at `20261019-r110-post-spec-review.md` and
  `20261019-r110-compiler-review.md`.
- Luna owns current state, the one command, closeout,
  `next_action_selector`, explicit-path Git integration and push.

No worker may run tests, builds, compiler/runtime probes, formatter, CLI or Git.
Only Luna's one exact command is authorized after CLEAN reviews. Preserve all
three inherited UNKNOWN identities, the board quarantine, R104 historical
lease and legacy slot reservation. At most two producers concurrently; do not
reclaim an unknown lease.

Total resource ceiling: 1,200 seconds: proof 360, implementation 240, fresh
pre/post spec 120 combined, compiler/source review 180, command 120,
integration/closeout 180; Astra 0. No renewal. Stop on pin mismatch, source
obstruction, review blocker/major, unexpected command result, or budget
exhaustion.

## Breadth boundary

This is one finite §21 entry-demand/CLI publication slice. The five other
effect-hygiene fronts, method/role obligations, R101/R102 source-entry gap,
original Simple-sub/evaluator quantifiers and semantic adoption gates remain
independent and open. The R109 source-range mismatch remains recorded and
untouched. The next selection should rotate again; no single effect front may
monopolize the sequence.
