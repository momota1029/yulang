# LEAN-CALL-REQUEST-BOUNDARY-20261025/r2 — adjudicated outcome

Status: **CLEAN independent review accepted by the primary; ready for integration.**
Full user goal: **OPEN**. Baseline: `4d15e26ff207993a8e9049fb21f754f219c0a273`
on `research/simple-sub-intrusion`.
Contract: [r2](call-request-boundary-20261025-r2.md), SHA-256
`b92747b9e519be2f9f3c14c01db0f1353a0a3ea461fb8633b0d25eb2ff27896f`;
r1 is retained unchanged with its failed-check handoff.

## Before, after, and application to the original goal

Before this sprint, the formal Call layer had existential request unwind and
separate capture/response typing. It did not identify every possible finite
request-prefix endpoint or connect an arbitrary actual completed request to the
response result. The new theorem proves, for arbitrary metadata, world, state
and natural-number prefix length, an exact iff between actual request prefixes
and the uniquely computed endpoint plus the derived `frames.length + 1` bound.
The partial equation exposes literal residual frames and captured syntax; the
complete equation exposes the ordered world/scope fold, observation context and
all retained fields. Completion occurs exactly at the bound, and no represented
Call transition can leave the requested state.

The composition theorem starts with an actual prefix from the existing typed
initial Call, appends the realized request completion, and applies existing
preservation and terminal inversion. A supplied closed typed response then
substitutes into that actual captured continuation, equals plugging the original
frames, and has the original result type. The companion theorem applies this to
any actual completed request trace. The entire represented request branch is
therefore characterized and connected to the typed response result, without a
new semantic assumption or restriction of the accepted source domain.

Full execution adequacy still needs viewed-Force source realization
(`FL12-SOURCE-1`, r12.1 outcome), raw Call successor coverage/erasure and source/native
request-response correspondence. Source/native metadata and response authenticity
are not inferred from the formal equations. Original Call/inference A/B,
source/native and production gates remain OPEN with their existing owners.
The primary owns intake of these missing source bridges and the next substantive
sprint. This milestone does not establish unrestricted Call progress.

## Authorship, repair and independent review

The r1 constructive author `/root/call_request_boundary_astra_r1` stopped after
its first Lean failure at 2026-10-25T04:38:04Z. The immutable failed-source hash and
failure receipt remain in the r1 handoff. The current primary repaired record
syntax and the induction step, strengthened the public result to all prefix
lengths using a decreasing rank, and constructed the actual-prefix composition.
The r2 contract authorized that repair after cessation; no dependency changed.

Fresh nonauthor `/root/call_request_boundary_review_astra_r2` inspected the actual
transition constructors, proofs, direct dependencies, full printed signatures,
axiom reports, falsifiers, import/output hashes and receipts. Its verdict was
**CLEAN**, with no blocking, major or minor finding. The primary accepts that
verdict for the exact reviewed hashes below. The reviewer contributed no proof
repair, reran no Lean/build/test, and reported STOPPED with no descendants or
running subprocesses. Final message was received by 2026-10-25T04:44:34Z.
Requested author/reviewer model and effort were Astra/medium; effective telemetry
is UNKNOWN. The current primary is user-selected; historical role names are not
model evidence.

## Checks and limitations

The r2 receipt contains five serialized `lake env lean -j1 -M1024` invocations,
totaling 2.203071898 seconds. Final rows 2, 4 and 5 check both final sources and
the signature/axiom/falsifier query, all exit 0 with no warnings or timeout.
Row 1 is an intermediate successful boundary check. Row 3 records a failed
composition elaboration followed by its correction and successful final row 4.
These development failures are preserved, not counted as successful checks.
The independent reviewer matched all frozen final input/import/output hashes.

All ten queried public theorems use only `[propext]`; no holes/custom axioms were
found. Fifteen checked examples distinguish noncommuting scope/view action order,
effect/result identities, nested capture syntax, bind/adapter order, binder
lifting, response indices, exact completion time, observation context, literal
suffix and an impossible extra transition. Universal coverage comes from the
proofs, not the finite examples. Exact query/source snapshots and full streams
are embedded in the durable JSONL, including scratch query content.

No production/compiler/runtime, fixture, expected-output or build-system edit was
made. `NO_SAFE_CODE_SLICE`: actual `runtime/machine.rs::return_value`,
`enter_template` and `runtime/receiving.rs::Receiving::delay` were inspected;
a checked encoding to their response/template/view owners is still missing.
No broad test suite or Cargo run occurred. Static scheduling checks remain
separate from proof evidence and runtime authentication.

Resources: 300 seconds charged to r1 author and 300 to fresh review, sequential;
the previous author budget was not reset. R2 used 5 of 12 allowed Lean calls and
2.203071898 of 240 allowed Lean seconds. The 1800-second r2 grant includes primary
repair, integration and contingency. The old r1 check used 3.060279394 seconds,
recorded separately. Three historical UNKNOWN workers/reservations remain
quarantined; none was reclaimed. All proof authors and reviewer have stopped
writing their frozen artifacts. Primary integration/current-state work continues.

## Frozen evidence hashes

- `notes/theory/lean/YulangClosure/CallRequestBoundary.lean`: `28ffc2943c18d324c35dacf18b4dd70921d4cc462ffd6ffdce989475ef46cce6`
- `notes/theory/lean/YulangClosure/CallRequestBoundaryComposition.lean`: `fed00f06cdbf2a5bdc1b3c18957acc33c7b281e890f277ca5bd1d20ece53ee76`
- `tasks/agent-loop/inbox/20261025-call-request-boundary-r2-review.md`: `d9887dc10b74b263a5a94795251299e6d53ed2f7bac6865d18858c33bd08cbf6`
- `tasks/agent-loop/inbox/20261025-call-request-boundary-r2-verification.jsonl`: `4df963ddb36e55246ef204a67f676633e26b2c0da3c4bb8782adcd8c7a53062d`
- `tasks/agent-loop/inbox/20261025-call-request-boundary-composition.md`: `4b56dae37c244c23a7bc6f59a34d9ff5da950ec0bb2b96e733598ff13b8e2f48`

The generated `.olean`/`.ilean` and scratch-query hashes are recorded in the
verification receipt and independent review. Generated `.lake` files are not
Git artifacts. The r1 handoff and both contracts are retained in the same
integration component.

## Git and compact-state handoff

At this receipt's freeze no new commit or push has yet occurred. Primary will
stage only the exact proof, contract, handoff, verification, review, this outcome
and current-state paths, inspect the complete outbound range, commit and push
without forcing. The resulting commit and push receipt belongs in current.json
after the operation; this immutable receipt makes no advance success claim.

The following prior history locators are archived verbatim from the primary
snapshot so current.json remains within its canonical 16 KiB limit. They are
resolved historical records, not live workers or newly closed parent obligations.
All pending parent entries and every UNKNOWN reservation remain in current.json.
The active sprint's frozen leases below remain until integration consumes them.

### Prior history locators

```json
[
  {
    "id": "FORCE-ADMIN-RESULT-DISCHARGE-20261025/r7",
    "record": "tasks/agent-loop/sprints/force-admin-result-discharge-20261025-r7-outcome.md",
    "commit": "9b7b4e00dd3862bf4bf0281594f3a658ba9fd59b"
  },
  {
    "id": "FORCE-SOURCE-REALIZATION-20261025/r8",
    "record": "tasks/agent-loop/sprints/force-source-realization-20261025-r8-outcome.md",
    "sha256": "4c63f6f55a4fd5ee2afeb83a5df575704715b7bc093a1934997b4cb4994ba5eb",
    "commit": "a8afc44cc26271b257e039c90b2443b77de9fa23"
  },
  {
    "id": "FORCE-PRODUCER-EXPORT-TRACE-20261025/r1",
    "record": "tasks/agent-loop/sprints/force-producer-export-trace-20261025-r1-outcome.md",
    "sha256": "bf544d639797fbecad878095916588d300eddf1e9c786d37786c9ebca01e232f",
    "commit": "cfea96fbe617f8a2017ca322961472e701e7bff7"
  },
  {
    "id": "FORCE-DECLARATIVE-CONSTRUCTION-20261025/r10",
    "record": "tasks/agent-loop/sprints/force-declarative-construction-20261025-r10.md",
    "sha256": "ddcfe7b8ff5065ab76dae1c753ad43a33b0f7ef38682ff4829dd218c2094e521",
    "commit": "cfea96fbe617f8a2017ca322961472e701e7bff7"
  },
  {
    "id": "FORCE-DECLARATIVE-CONSTRUCTION-20261025/r10",
    "record": "tasks/agent-loop/sprints/force-declarative-construction-20261025-r10-outcome.md",
    "sha256": "5f445c4e693387496a3d9a232c9ed9f273509dd6c1f71aa6e6de8e890f80c62d",
    "commit": "cfea96fbe617f8a2017ca322961472e701e7bff7"
  },
  {
    "id": "FORCE-COMPLETION-20261025/r11",
    "record": "tasks/agent-loop/sprints/force-completion-20261025-r11-outcome.md",
    "sha256": "e38b47c52a25d5a3561f2823e55be23129bd8cc920fabdbf3d3561ae0c454b6a",
    "commit": "e2d3f14bd795f7ef4e61f6453b3a5d4dc38b80dd"
  },
  {
    "id": "FORCE-LOCAL-APPLICABILITY-20261025/r12",
    "record": "tasks/agent-loop/sprints/force-local-applicability-20261025-r12-outcome.md",
    "commit": "PENDING"
  },
  {
    "id": "FORCE-LOCAL-APPLICABILITY-20261025/r12.1",
    "record": "tasks/agent-loop/sprints/force-local-applicability-20261025-r12-outcome.md",
    "sha256": "c790537a61232946a2e01c5d67551a05207f2c07f839839902978acf9144a5b4",
    "commit": "f4bf568a07cdeaa310aae0b30aa19d31d6580cbf"
  },
  {
    "id": "LEAN-CALL-CONTEXT-TYPING-20261025/r3",
    "record": "tasks/agent-loop/sprints/call-context-typing-20261025-r3-outcome.md",
    "sha256": "98b9a65a899264cf739ad0ee42ed104e2c01716f530c9d11b561a9f2a0d1e9d3",
    "commit": "f105e0ce0"
  },
  {
    "id": "LEAN-CALL-ENTRY-SPINE-20261025/r1",
    "record": "tasks/agent-loop/sprints/call-entry-spine-20261025-r1-outcome.md",
    "sha256": "11f2478ec74c36fa14c46b66a9027dc9bc8f3fce2e62f6c0356ab8063989c8bb"
  },
  {
    "id": "LEAN-CALL-ENTRY-SPINE-20261025/r3",
    "record": "tasks/agent-loop/sprints/call-entry-spine-20261025-r3-outcome.md",
    "sha256": "da4481a11082779b090563f7d7511652e39958b4ee48511de652ed4046cca9c1",
    "commit": "12a081b82e2a84678aab7f5d0f301cd724c72542"
  },
  {
    "id": "LEAN-CALL-STEP-TYPING-20261025/r1",
    "record": "tasks/agent-loop/sprints/call-step-typing-20261025-r1-outcome.md",
    "sha256": "d7606d506a52be722e4504cce91eee1b76c73df14659b3b67eb6b2b4f4dfa158",
    "commit": "862c8777684587f6ca2b20d22859f954804a2c50"
  },
  {
    "id": "LEAN-CALL-STEP-TYPING-20261025/r2",
    "record": "tasks/agent-loop/sprints/call-step-typing-20261025-r2-outcome.md",
    "sha256": "803dbc0e9724a18149bebf7bc40965c144bbfcefe3c9bce879333c40a9a0ac20",
    "commit": "577285ec9"
  },
  {
    "id": "LEAN-CALL-FINITE-TYPING-20261025/r1",
    "record": "tasks/agent-loop/sprints/call-finite-typing-20261025-r1-outcome.md",
    "sha256": "f82192a95c9d5cac2474160e56654ffa6b36fa737edca09fd443b3b0fab1456d",
    "commit": "3bbd875a8"
  },
  {
    "id": "LEAN-CALL-UNWIND-20261025/r1",
    "record": "tasks/agent-loop/sprints/call-unwind-20261025-r1-outcome.md",
    "sha256": "331aab9fffd7f17fe7cbfdae98d723111a7a331b92cb672a7012a664557ef405",
    "commit": "33cd9e0a5"
  },
  {
    "id": "LEAN-CALL-UNWIND-20261025/r2",
    "record": "tasks/agent-loop/sprints/call-unwind-20261025-r2-outcome.md",
    "sha256": "8ad36a0dbcb99faf2a87164b4fcd87e21754f1c40583fee963bd95b267d8655c"
  },
  {
    "id": "LEAN-CALL-PROGRESS-OBSTRUCTION-20261025/r2",
    "record": "tasks/agent-loop/sprints/call-progress-obstruction-20261025-r1-outcome.md",
    "sha256": "dc329ddc99486ff2ae375b6f398721cbcabacde7ea9de67c9f8f7398a67e0176"
  },
  {
    "id": "LEAN-CALL-PROGRESS-OBSTRUCTION-20261025/r3",
    "record": "tasks/agent-loop/sprints/call-progress-obstruction-20261025-r3-outcome.md",
    "sha256": "84381305fb3446effb694ddf814a22af45a6115941b7dcc7259fbe38dacdfa6c",
    "commit": "0c7ce488f"
  },
  {
    "id": "FORCE-SOURCE-REALIZATION-20261025/r2",
    "record": "tasks/agent-loop/sprints/force-source-realization-20261025-r2-outcome.md",
    "commit": "b2b6bae2e"
  },
  {
    "id": "FORCE-PROJECTION-DESIGN-20261025/r3",
    "record": "tasks/agent-loop/sprints/force-projection-design-20261025-r3-outcome.md",
    "commit": "d9862f4a0"
  },
  {
    "id": "FORCE-SOURCE-EQUATIONS-20261025/r4+r5",
    "record": "tasks/agent-loop/sprints/force-source-mapop-correction-20261025-r5-outcome.md",
    "commit": "8f789f8f5"
  },
  {
    "id": "FORCE-ADMIN-RESULT-DISCHARGE-20261025/r6",
    "record": "tasks/agent-loop/sprints/force-admin-result-discharge-20261025-r6-outcome.md",
    "commit": "79e71c17d"
  },
  {
    "id": "LEAN-CALL-CAPTURE-RESPONSE-20261025/r1",
    "record": "tasks/agent-loop/sprints/call-capture-response-20261025-r1-outcome.md",
    "sha256": "d6bd96f5df49a3e2b00574e87eff6b07b79add75c749e3a57d761da264c41606",
    "review": "tasks/agent-loop/inbox/20261025-call-capture-response-r1-review.md",
    "review_sha256": "1d94a31da7822060f6fafe1131b8cdd943843c0625f85fc1c337cf86a470af5b",
    "commit": "45ebac6b3"
  }
]
```

### Frozen current-sprint owners and leases

```json
{
  "workers": [
    {
      "id": "/root/call_request_boundary_astra_r1",
      "role": "bounded constructive proof author",
      "state": "STOPPED",
      "session": "LEAN-CALL-REQUEST-BOUNDARY-20261025/root-turn-15",
      "requested_model": "gpt-6-astra",
      "requested_effort": "medium",
      "observed_model": "UNKNOWN",
      "observed_effort": "UNKNOWN",
      "receipt": "Final handoff: writes stopped 2026-10-25T04:38:04Z; no descendants or running subprocesses; r1 check exit1; 300s charged."
    },
    {
      "id": "/root/call_request_boundary_review_astra_r2",
      "role": "independent proof reviewer",
      "state": "STOPPED",
      "session": "LEAN-CALL-REQUEST-BOUNDARY-20261025/root-resume-r2",
      "requested_model": "gpt-6-astra",
      "requested_effort": "medium",
      "observed_model": "UNKNOWN",
      "observed_effort": "UNKNOWN",
      "receipt": "Frozen CLEAN report/final message received 2026-10-25T04:44:34Z; writes STOPPED; no descendants or running subprocesses; 300s charged."
    }
  ],
  "leases": [
    {
      "path": "tasks/agent-loop/sprints/call-request-boundary-20261025-r1.md",
      "owner": "/root",
      "state": "FROZEN",
      "reason": "frozen exact r1 contract; hash pinned"
    },
    {
      "path": "notes/theory/lean/YulangClosure/CallRequestBoundary.lean",
      "owner": "/root",
      "state": "FROZEN",
      "reason": "r2 primary repair after actual writer STOP."
    },
    {
      "path": "tasks/agent-loop/inbox/20261025-call-request-boundary.md",
      "owner": "/root/call_request_boundary_astra_r1",
      "state": "FROZEN",
      "reason": "Immutable r1 failed-check handoff; author STOP acknowledged."
    },
    {
      "path": "notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallRequestBoundary.olean",
      "owner": "/root",
      "state": "FROZEN",
      "reason": "r2 primary repair after actual writer STOP."
    },
    {
      "path": "notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallRequestBoundary.ilean",
      "owner": "/root",
      "state": "FROZEN",
      "reason": "r2 primary repair after actual writer STOP."
    },
    {
      "path": "notes/theory/lean/YulangClosure/CallRequestBoundaryComposition.lean",
      "owner": "/root",
      "state": "FROZEN",
      "reason": "primary composition after Astra STOP"
    },
    {
      "path": "tasks/agent-loop/inbox/20261025-call-request-boundary-composition.md",
      "owner": "/root",
      "state": "FROZEN",
      "reason": "primary composition handoff"
    },
    {
      "path": "notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallRequestBoundaryComposition.olean",
      "owner": "/root",
      "state": "FROZEN",
      "reason": "generated output exact lease"
    },
    {
      "path": "notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallRequestBoundaryComposition.ilean",
      "owner": "/root",
      "state": "FROZEN",
      "reason": "generated output exact lease"
    },
    {
      "path": "tasks/agent-loop/sprints/call-request-boundary-20261025-r2.md",
      "owner": "/root",
      "state": "FROZEN",
      "reason": "r2 exact lease"
    },
    {
      "path": "notes/theory/lean/.lake/call-request-boundary-r1-failed.lean",
      "owner": "/root",
      "state": "FROZEN",
      "reason": "r2 exact lease"
    },
    {
      "path": "notes/theory/lean/.lake/call-request-boundary-r2-check.lean",
      "owner": "/root",
      "state": "FROZEN",
      "reason": "r2 exact lease"
    },
    {
      "path": "notes/theory/lean/.lake/call-request-boundary-r2-run.py",
      "owner": "/root",
      "state": "FROZEN",
      "reason": "r2 exact lease"
    },
    {
      "path": "tasks/agent-loop/inbox/20261025-call-request-boundary-r2-verification.jsonl",
      "owner": "/root",
      "state": "FROZEN",
      "reason": "r2 exact lease"
    },
    {
      "path": "tasks/agent-loop/inbox/20261025-call-request-boundary-r2-review.md",
      "owner": "/root/call_request_boundary_review_astra_r2",
      "state": "FROZEN",
      "reason": "fresh nonauthor review report"
    },
    {
      "path": "tasks/agent-loop/sprints/call-request-boundary-20261025-r2-outcome.md",
      "owner": "/root",
      "state": "HELD",
      "reason": "r2 exact lease"
    }
  ]
}
```
