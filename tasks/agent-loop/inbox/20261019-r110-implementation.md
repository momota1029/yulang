# R110 implementation handoff

Status: FROZEN. Contract: `tasks/agent-loop/sprints/cli-entry-demand-20261019-r110-rev1.md`.

## Contribution

Added exactly one integration test, `entry_demand_controls_cli_completion`,
at `tools/inference-playground/tests/cli_entry_demand.rs`. It runs two child
processes serially, each with stdin and the exact arguments
`--run main --steps 10000 -`. The first receives the Value source and asserts
unsuccessful exit, empty stdout, and the existing 10,000-step exhaustion
diagnostic. The second receives the Computation source and asserts successful
exit, stdout exactly `9\n`, and empty stderr.

The source prefix and body strings are concatenated without appending a final
LF. Static byte-count and SHA-256 checks match the frozen contract:

- Value source: 97 bytes, `1c1d1d5d98c1acc3148f199408cb1324a4c1fee3aa4474034ed7495d7ee54446`.
- Computation source: 106 bytes, `ac926feeb27c26d81f8545ac05810dbcf7f8dd60719b84fee316db2417b8ec73`.
- Test file: `283e3518f8d28efedd171cacfe97fc7246225339b1c160d06b3c58944f86c8bc`.

## Evidence reused and limits

The inspected frozen dependency pins matched the R110 contract: `cli.rs`,
`cli_entry_publication.rs`, `main.rs`, `lib.rs`, `output.rs`, `Cargo.toml`, and
R97's `runtime_control.rs`. R97's implementation handoff provides the prior
finite Value/Computation runtime contrast; R105's implementation handoff and
the existing CLI publication test provide the serial stdin subprocess pattern.
These sources justify the test construction only; no test result is inferred.

The test connects the two exact source inputs to finite CLI status and stream
observations if Luna's one authorized command passes. It does not establish
mathematical divergence, a universal §21 theorem, source-wide CLI soundness,
effect hygiene, Simple-sub/evaluator correctness or semantic adoption.

## Checks and resources

- No test, build, compiler/runtime probe, formatter, CLI invocation or Git
  command was run by this lane.
- Static source byte-count and SHA-256 checks only; frozen source identities
  match exactly.
- Requested model/effort: Luna/high. Observed model/effort: unavailable in this
  worker interface.
- Exact active-work time: unavailable; the assignment stopped within the
  240-second ceiling.
- New paths: this test and this handoff only. No scratch files were created.

## Next related step

Freeze these outputs for independent post-output spec and compiler/source
review. After both reviews are CLEAN, Luna owns the single exact command in the
contract. A failure, source-preparation rejection or unexpected diagnostic
must be preserved without repair or retry.
