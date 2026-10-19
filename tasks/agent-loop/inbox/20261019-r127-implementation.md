# R127 implementation handoff

Status: output frozen; STOPPED.

Added one paired test,
native_operation_payload_role_controls_publication, for the exact 92-byte
Value source and 95-byte Computation source, both without final LF. It
authenticates the expected CallTail Apply in each main definition's
LocalSource and joins its callee to the HIR-owned resolved ping declaration.
The Value Machine assertion expects fuel exhaustion at exactly 1,000 steps.
The Computation Machine assertion expects UnhandledRequest with that Apply's
same source root, occurrence and range, the same ping identity, Computation
payload, and a nonempty saved continuation.

The public stdin CLI assertions require Value failure with empty stdout and
exact stderr bytes "runtime step budget exhausted after 1000 steps; no completed result\n";
Computation failure with empty stdout and exact stderr bytes
"unhandled runtime request at 84..93\n". Both byte assertions include exactly
the terminal LF. These are requested finite observations; fuel exhaustion is
not claimed as a divergence proof.

Contract tasks/agent-loop/sprints/native-payload-entry-cli-20261019-r127-rev3.md
SHA-256 04b707e493f53e1fe35747c11ec1fadb57238a560e9f37d6b57d4865fb04fa7f.
All 31 listed inputs matched before writing. Exact source hashes are
Value a620b984fea7f339da2adcf4acfd053725fcf10e63861efc20a0f8e769b5189e;
Computation 7041a3314180f4438ca717794bbaaf7b5dc2e904096211f0682df2d14969bbbc.
No production code, existing test/fixture/diagnostic, or expected output
changed. No tests/builds/CLI/probes/formatter/Git actions, scratch paths, or
child workers were created. The new test was not run or independently reviewed.

Implementation cap is 240 seconds. Elapsed time was not instrumented; charge
the full 240 seconds conservatively. Requested Luna/high; observed
UNKNOWN/UNKNOWN. Only the two leased paths were written. STOP.
