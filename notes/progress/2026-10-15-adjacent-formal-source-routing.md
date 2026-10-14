# Adjacent named formals in the source candidate

Date: 2026-10-15
Status: implemented, independently reviewed and observed through the actual CLI
Baseline: `72e156f77d32efea98eeb06b3f54a98fdc9395c0`

The user's exact `my relay(thunk: [signal] int) = ...` spelling parsed as a
`PatternCallTail`, while the source HIR header accepted only the spaced ML
tail. The parser's existing glued call syntax is governed by the October 14
operation-pattern-tail decision; no grammar change is made here.

`module.rs::plain_binding_header` now admits one recovery-free adjacent named
parameter, optionally annotated, in `local_source` mode. It retains the real
identifier/source key and original annotation node through `AdmittedParameter`.
Both definition and local-binding callers use this same owner. The spaced ML
branch and non-source modes are unchanged. Unit, multiple, chained and
destructured parameters remain outside this candidate carrier's existing
support; no synthetic parameter or parameterless reinterpretation is used.

M1, one independent `regression_auditor` (`review_adjacent_formal`) inspected
the changed branch, direct root/local consumers, recovery, original source
identity and ML sibling. No blocking finding remained. Persistent regression
coverage is not added because this task's tool instructions prohibit
unsolicited test additions/runs.

One serialized playground build passed without warnings:
`CARGO_BUILD_JOBS=2 timeout 300s cargo build -q -p yu-playground`.
It also compiled the private scoped algebra module; do not count that shared
build twice when totaling processes. Five bounded direct executions (30-second
cap each), retained under `/tmp/yulang-computation-route-85zlnid9`, showed:

- Exact adjacent annotated thunk/Catch source solves.
- Exact adjacent unused Computation source permits an empty-effect result.
- Exact adjacent forced Computation source conflicts with an empty-effect result.
- An adjacent local formal inside a block solves through the same HIR owner.
- The exact callback annotation now reaches the existing solver limitation:
  composed-negative concrete callback effects remain unsupported.

This CLI does not execute return values, and Catch still forwards effects.
No claim of returning `1`, removing signal, or completing handler hygiene is
made. No tests or benchmarks were run. The solver callback-permission and
Catch-removal owners remain OPEN.

One additional source execution repaired the earlier *observation input*
`both()` to a supported named formal `both ignored`; the supplied computation
emitted both signal and write and was accepted at `[signal]`. This corroborates
the absence of a closed input cap, but no exact residual subtraction is yet
observed. The original unsupported unit-formal runs remain recorded.
