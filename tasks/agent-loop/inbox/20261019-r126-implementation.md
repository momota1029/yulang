# R126 implementation handoff

Status: output frozen; STOPPED.

Added one paired test,
normal_value_arm_runs_after_shallow_handler_exit, for the exact 80-byte control
and 105-byte outside-arm source fixtures, both without a final LF. The typed
Machine control must complete with integer 7. The outside case must be an
unhandled request for the HIR-owned ping operation, with Unit payload and a
nonempty continuation. Its SourceSite is checked against the same main
definition's LocalSource Apply at CallTail range 101..103; the Apply callee is
checked as the resolved ping operation and its argument as Unit.

The paired public stdin CLI observations require control success, stdout 7
followed by LF, and empty stderr; outside-arm failure, empty stdout, and exact
stderr unhandled runtime request at 101..103 followed by LF. These are finite
observations, not a general handler theorem.

The rev2 contract
tasks/agent-loop/sprints/normal-value-arm-outside-20261019-r126-rev2.md
has SHA-256 80b994bb759e12f19888512fc2d99c0563eb6497a58e3af3db1b023123237be8.
All 30 listed input hashes matched before writing. No production code,
existing test/fixture, diagnostic, proof path, or expectation changed. No
tests/builds/CLI/probes/formatter/Git were run. No scratch paths or children
were created. The exact new test remains unrun and unreviewed by its author.

Producer cap: 300 seconds. Elapsed time was not instrumented; conservatively
charge the full 300 seconds. Requested Luna/high; observed UNKNOWN/UNKNOWN.
Only tools/inference-playground/tests/cli_value_arm_outside.rs and this handoff
were written. STOP.
