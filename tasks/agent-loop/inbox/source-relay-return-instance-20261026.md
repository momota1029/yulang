# Source owner handoff: relay return instance

Sprint: `SOURCE-RELAY-RETURN-INSTANCE-20261026/r1`  
Contract SHA-256: `cb69afdf901bd1fbb0a5838da6af46ef55de50609c345e61cec144b19da9396f`  
Baseline: `cc99471f36b167a8cfd526c5853f1c12077aaf58`; Lean tree pin:
`7b01b90fb48db71e832a1ff46a78df2b486d6b1a`  
Claim: construct actual source `T` and same-execution result/consumer
correspondence for the pinned `relay` fixture. Original full A/B and
source/native parent gates remain OPEN.

## Result and correspondence

The source note records the actual Parameter/Name/Lambda/Result/Delay/Call
constructor spine, source instance, original `xi=(nu,K,D)`, scopes and
provider/receiver correlations. It traces `relay`'s Value entry through actual
Force, Return/rebind, Name and Result; for any finite request/resume history,
the original suffix resumes at the current world, and only an actual Return
fills `W`. The identity result fact is established for returning executions,
without asserting termination of every challenge.

The same Call's actual `C.result` supplies `rho_C(C.result.q)=q` and excludes
`C.effect`; `mu` is identity because the actual relay body returns its Name
binding unchanged. The source note applies ReturnView to this same execution
and identifies the later complete `ExecuteCallable` consumer at the actual
call port. This is a partial constructor derivation, not full independently
typed `T`: the annotation's complete profile realization and independent
contextual challenge/carrier premises remain OPEN. The lambda identity at
`Int` has the same limitation. No body-safety, callee-acceptance, `LocalLaws`,
profile validity or desired export validity is used as an assumed premise.

Native owner correspondence is limited to existing Lambda entry, Name/read,
Return and complete-Call owner equations in the frozen native report. No claim
is made that raw HIR/native inference constructs the full source derivation,
that runtime stores `rho_C`, or that native Function values reach the required
later consumer. Rust remains `NO_SAFE_CODE_SLICE`. No nested-effect instance
was constructed; the first missing premise is independent annotation/profile
realization plus authentic challenge/consumer obligations. This is not a
counterexample.

## Reused and rejected evidence

Reused: `2026-10-16-runtime-function-result-source-construction.md` §§3–4 and
its ReturnView/FL12 extraction; `2026-10-16-runtime-function-result-view-projection.md`
§§3–5; the existing source-Generalize constructor table and contextual
Function membership definition; the typed-core selected Lambda entry and
complete `ExecuteCallable` meanings; and the reviewed native producer/consumer
equations in `2026-10-26-force-return-producer-correspondence.md`.

Rejected as substitutes for source construction: the fixture's compilation
or test occurrence, annotation shape, native Function pointer equality,
`PaperComputationTyped`, desired `CallableExport` validity, body safety,
callee acceptance, and a generic missing-exporter/field-name audit. The pinned
fixture occurrence is visible at `machine.rs:3118`; this is not evidence that
the full source `T` is constructed by inference.

## Premise ledger and exact remaining work

The leased source note contains the per-premise ledger. Constructed: original
syntactic owners; source-rule identity-return spine; same-execution result
edge and return binder; `rho_C` application; identity `mu`; actual complete
Call consumer owner. Partially supplied: entry/body operation on each actual
challenge. Missing: independently formed full callable challenge domain and
whole-carrier admission, profile/annotation realization at both Lambda owners,
universal actual-provider acceptance and full observations under original
contracts/current worlds, and raw source/HIR-to-judgment correspondence.
The pure row does not entail a vacuous challenge set or termination. Fixed
fixture data are distinguished from universally quantified admitted
challenges; no satisfying `xi` or concrete challenge inhabitants are invented.

No nested-effect source instance was built because its annotation/profile and
challenge/consumer premises are not constructed from the available original
rules/evidence in this pass. The precise falsifier is circular admission via
the desired safety/acceptance conclusion or shape-only profile inference. No
source-specific execution counterexample is asserted.

Concrete components available to registered Lean formalization: (a) a
constructor spine indexed by the two actual Lambdas and Name/Result binding
identities; (b) the returning-path relay identity equation; (c) a dependent
same-execution `C.result`/`W` binder with result-prefix removal and effect
exclusion; and (d) the complete-call consumer owner correspondence. Formalizing
these as actual source judgments requires the Lean source language to express
the selected Parameter, Name, Lambda-entry, Result, Delay and Call premises.
If it does not, report the missing source definition and leave the affected
component OPEN; do not replace it with an assumed `T` or new calculus.

## Diff, resources, and cessation

Only these leased paths were written:

- `notes/theory/2026-10-26-source-relay-return-instance.md`
- `tasks/agent-loop/inbox/source-relay-return-instance-20261026.md`

Checks/probes/builds/tests/Cargo/Git/network: 0. Children/descendants: 0.
Active seconds used: not instrumented; exact usage UNKNOWN, within the
1200-second source cap. Requested model/effort: Luna/high role default.
Observed model/effort/session metadata: UNKNOWN (runtime did not expose it).
Status: STOPPED; writes stopped; no descendants. This source candidate has
not received fresh non-author review and is not self-certified.

Dependency files were read only and not changed. The source result construction,
ReturnView projection, force-return native correspondence, source-Generalize,
contextual membership, typed-core, contract, fixture and Lean tree remain at
their frozen pins. No new dependency or authority is requested. The primary
owns any next related action: adjudicate the missing annotation/profile and
challenge realization premise, or pass the concrete components above to the
registered proof lane under its existing exact lease.
