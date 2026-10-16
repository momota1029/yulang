# Sprint: forward realization of the original NPAIR source witness

ID: `npair-forward-source-witness-realization-20261017`.
Status: READY; author starts only after exact pin and lease receipt.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN.
Primary: Luna/high, authority and sole Git integrator.

## Fixed outcome

Continue the original receive proof by supplying the original complete
Operation contribution witness `w` and its dependent scope at the source
boundary, then follow that same witness forward through actual Operation
seed/emission/admission, checked FunctionPort and ordered Replay premises, and
the recovered concrete Permission port.

Determine whether this forward realization validates the adopted
`At(D,w,delta)` or establishes only native structural incidence. If it cannot
reach the full dependent association, identify the exact missing original
constructor premise and owner. Apply the result to the original receive
obligation without narrowing its provider, observation, assignment, world,
typed-position, continuation, interaction, Call-demand or future quantifiers.

Starting with original `w` is a proof method, not an assumption that native
identifiers reconstruct it. The author must construct the source-to-native
correspondence from independently supplied source premises. Do not select the
first Origin, assume source admission, use the uncalled `f0` as a provider, or
invent an event ID. Preserve alternatives and distinguish original witnesses
from Operation member identity, Contribution identity, row identity and
processing derivations.

Success is either a constructive forward realization of the original witness
through the actual native path or a precise missing-premise result that names
which owning source constructor must supply it. A structural certificate alone
does not establish adopted `At`, source reachability, or parent closure.

## Frozen baseline and direct dependencies

Baseline: `ad2fbba0871ea96a9e6dadca92354cfb094a874a` (committed reviewed
proof/readiness frontier).

Previous sprint contract revision 3:
`tasks/agent-loop/sprints/npair-applied-producer-and-seed-bridge-20261017.md`,
SHA-256 `4e4f0c9797044b8395305775d7c45192a10300ee9b9bceb7a7d0a15ddae1f883`.
Its exact proof and readiness manifests are pinned in their frozen artifacts.

Frozen proof/readiness inputs:

- prior bridge proof `notes/theory/2026-10-17-npair-applied-producer-seed-bridge.md`,
  SHA-256 `45cfefb49b6a1ca567ea603558c95b0dfed22a776b23d3b5ed200e373befa579`;
- proof handoff SHA-256
  `986c4391063348592d6be13c9db549692b1fdcefcbc5eb72dd1ad5da68150a12`;
- descriptor-seed readiness Draft SHA-256
  `9f4e2d9f2ccc6f972d9a6eb99910a0e9a44c982eda0646f512f687ec9d518395`;
- readiness handoff SHA-256
  `b96b55b05992748f89842e417ce035f83a9df6cce12109043d28ec1a295c5dde`;
- applied native-port design SHA-256
  `a6b6f37218408b334922c19ff6065bd8bd607294201ec2b371f1376e800c41ce`;
- approval receipt SHA-256
  `cd81ea1385b1304da283ef8ee15cdd626b98d1759cf79aa372f672e53c5bab67`.

Original adopted semantics and independent Operation/Call clauses:

- adopted negative-pair proposal
  `notes/design/2026-10-17-negative-formal-pair-formation-proposal.md`,
  SHA-256 `0a73aaf7016e86dd5babbdd5482b05a793764418bc003607207ef0375ee46006`;
- proposal adoption receipt
  `notes/design/2026-10-17-source-formation-proposals-adoption.md`,
  SHA-256 `d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa`;
- adopted parent construction
  `notes/theory/2026-10-17-adopted-negative-pair-construction.md`,
  SHA-256 `6a3c6b5754448b38430ee368feb52d87ebd38c1b7050c3b33652132ead5f0fb2`;
- original Call source interface
  `notes/design/2026-10-08-call-source-interface-definition.md`,
  SHA-256 `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c`;
- governing inference principles
  `notes/design/2026-10-11-yulang-inference-top-level-principles.md`,
  SHA-256 `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`;
- Operation instance/dependent-scope package
  `notes/design/2026-10-02-operation-instance-binding-package.md`,
  SHA-256 `1eb2cbdb49368b0839d839d6a5e72698bb06252813b00200098e70371645c7c9`.

Exact current native source dependencies to verify before reliance:

- `crates/yu-solver/src/candidate_effect.rs`:
  `11a1477ff2c35c03dccb70bdc6121d89d3ced9fadb1921cb8cf8cd5c093b07fb`;
- `crates/yu-solver/src/candidate_source.rs`:
  `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38`;
- `crates/yu-solver/src/candidate_context.rs`:
  `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6`;
- `crates/yu-solver/src/candidate_scheme.rs`:
  `52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a`;
- `crates/yu-solver/src/candidate_extrusion.rs`:
  `2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b`;
- `crates/yu-solver/src/shadow_apply.rs`:
  `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf`;
- `crates/yu-solver/src/lib.rs`:
  `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f`;
- `crates/yu-hir/src/shadow.rs`:
  `2dffd7fd6542eed9fd3346e0672e76197c248be9c84334f341c4d612234b7ee9`.

Any directly consumed definition outside these pinned inputs needs an exact
pin before reliance; mismatch stops only the affected proof claim and returns
to Luna. The original current source refusal remains part of the baseline, not
a source language exclusion.

## Lanes, leases and resources

Proof lane: `astra_prover`, medium, 900 seconds, at most six substantive stages.
Write only:

- `notes/theory/2026-10-17-npair-forward-source-witness-realization.md`
- `tasks/agent-loop/inbox/20261017-npair-forward-source-witness-realization.md`

Stages: (1) verify authority, all pins and define the exact original dependent
`w`; (2) construct or expose the source Operation contribution witness at its
actual source origin; (3) relate the same `w` to Operation seed/member,
physical emission and exact admission without discarding dependent coordinates;
(4) carry `w` through each actual FunctionPort and ordered Replay step to the
recovered Permission port, retaining relation alternatives; (5) classify
whether the native path validates `At(D,w,delta)` or only structural incidence,
and isolate the exact missing premise if not; (6) apply the result to the
original receive obligation and freeze. No descendants.

After proof author STOP and Luna intake, implementation-readiness lane:
Luna/high, 600 seconds. Write only:

- `notes/design/2026-10-17-npair-forward-witness-ingress-code-contract.md`
- `tasks/agent-loop/inbox/20261017-npair-forward-witness-ingress-code-contract.md`

The readiness contract must separate (a) structural certificate validation,
(b) semantic witness realization and adopted `At`, and (c) source admission.
It must specify existing and later lowers, alternatives/cycles, lifecycle,
bounded work/accounting and failure disposition. If semantic realization is
not established, describe only the justified native validator boundary; do not
design an `At` consumer or source preflight edit.

Fresh sequential reviewers after both outputs freeze: compiler-referee 120s,
architect 120s, spec-auditor 120s. No tests, builds, probes, source execution
or compiler lease. Coordination cap 120s; reserve 120s. Total fresh envelope
2100 seconds; no carryover. Authors run sequentially; unknown historical
reservations and the quarantined board lease remain intact.

## Non-goals and stop conditions

No source admission change, negative formal source lowering, N-Ingress consumer,
N-Transport, `rho_u`, receive consumer, subtraction, mixed/multiple-symbolic
or explicit-empty support, F1/FK1 closure, source-Generalize closure,
soundness/principality result, or production promotion. No expected-output,
fixture or diagnostic changes. Do not equate interface member with original
`w`; do not infer dependent coordinates from family, row, occurrence, selected
Origin or Contribution ID. Stop on an unpinned dependency, contradiction,
source event absent without a source owner premise, or need for new semantic
identity. Freeze the exact gap and return it to Luna without expanding leases.
