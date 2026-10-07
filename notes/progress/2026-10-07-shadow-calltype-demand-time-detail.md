# Shadow locator for the CALL_TYPE demand-time premise

Date: 2026-10-07
Baseline: `08c1e1aa8faa97366f78b907b7b13e8b7477f11d`
Status: default-off evidence-plumbing slice; compiler-referee reviewed; no semantic adoption
Scope: one static detail locator on an existing unresolved Apply premise

## Result

The existing per-Apply
`JointArgumentTypingAndActualReturnedProviderCarrierCompatibility` premise
now exposes one borrowed/static candidate detail:

```text
CandidateWholeArgumentDemandTimeCapturedBindingsAndDelayInterpretation
```

This names the C5/C6 route in the research-only
[operand-clause candidate](2026-10-07-call-type-operand-context-clause-candidate.md).
The premise row, its Apply identity, inventory order, solver state and
production routing are unchanged. The accessor adds no stored field or row.
It returns no detail for any other premise.

The detail is a locator, not evidence. It asserts no Delay, applicability,
provider, world, `xi`, captured-binding judgment, `RunCert`, carrier membership,
compatibility or satisfaction. C5/C6 remain unadopted. The full conjunction
must remain intact; demand-time captured-binding adequacy is not established by
capture identity or by pointwise typing at the callee-return world.

## Structural and verification evidence

Focused assertions select the detail only on the existing joint premise and
preserve its Apply identity through HIR, Core and solver observations. Grouped
calls retain eight common pending rows; direct-use calls retain ten; computed
calls preserve their per-Apply six/eight-row distinction. No inference fact or
constraint is emitted and `ApplicationTypingRuleUnresolved` remains intact.

Checks:

- `RUSTC_WRAPPER= cargo test -p yu-hir --features shadow shadow::tests:: -- --test-threads=1` — 27 passed.
- `RUSTC_WRAPPER= cargo test -p yu-core --features shadow --test shadow_feature -- --test-threads=1` — 3 passed.
- `RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-f5 --test shadow_captured_source_retention -- --test-threads=1` — 4 passed.
- `rustfmt --edition 2024 --check` on the three changed Rust files — passed.
- `git diff --check` — passed.

The independent compiler-referee review passed with no findings. The default
sccache wrapper failed with EPERM; focused checks succeeded with
`RUSTC_WRAPPER=`. No broad suite, default-feature build, or performance
measurement was run. The reviewer and producer ran no overlapping Cargo
processes.

## Semantic frontier and gate status

Under the candidate whole-carrier criterion, the exact fixed-Name argument
leaf is: at every independently admitted demand world, the original `x`
binding must satisfy its independent value/provider/captured-dependency
judgment jointly with world and incidence evidence. This exceeds lexical
identity transport from `C0` to the callee-return world `C1`. If `DelayIntro`
is separately supplied, the next CALL_TYPE leaf is joint `CI-Receipt` input
construction. Neither clause is derived here; this note makes no status claim.

At the baseline, the canonical DAG had 90 nodes / 196 edges:

```text
CLOSED 7
CONDITIONAL-CLOSED 20
OPEN-PROOF 43
OPEN-SEMANTIC 19
IMPLEMENTATION-ONLY 1
```

The focused implementation slice does not reduce these counts. CALL_TYPE stays
CONDITIONAL-CLOSED with its independent `SEM_JOINT` premises; HIR_WIRING stays
IMPLEMENTATION-ONLY; production Apply remains unsupported. Production
inference and cutover are unchanged.
