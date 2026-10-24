# LEAN-COMPLETE-CALL-20261025/r7 outcome

Status: **CHECK_FAILED / UNACCEPTED**. This is a failed, research-only
checkpoint of an unchecked representation candidate. It is not a theorem,
source/native result, accepted implementation, or production approval.

## Goal and result

The unchanged parent goal is complete Lean proofs for Yulang semantics and
type inference under `notes/theory/lean`. R7 attempted a typed Call fragment
and two bounded safety propositions. The fragment was frozen, but its first
pinned Lean module did not elaborate. Proposition A,
`call_context_plug_preservation`, and Proposition B,
`bounded_call_finite_prefix_safety`, remain OPEN and have no Lean proof files.
No independent review ran. The full parent, original inference A/B,
source/native correspondence, principality, and termination remain OPEN.

## Exact check receipt

Luna ran one serialized check from `notes/theory/lean`:

```text
timeout 120s lake env lean -j1 -M1024 YulangClosure/CoreSyntax.lean
exit 1; elapsed 3.55s; 33 Lean elaboration/type diagnostics
```

Reported blockers include unavailable `DecidableEq` for `Original.Ty`,
declaration-order/missing-name errors (`ViewOccurrence` before `PortPath`, and
`InterfacePorts` before `Adapter`/`InterfacePlan`), the reserved identifier
`instance`, forbidden Prop elimination from `FunctionTyped`, and downstream
unknown identifiers caused by those errors. Further payload-type errors were
observed in `requestScope`, `requestExpose`, and `finishRequest` (their
computation payloads do not match the request value payload). No dependent
module or root-module check ran. This is an elaboration failure, not a semantic
counterexample or proof result.

`python3 tools/agent_sprint.py check` passed as workflow-state validation only.
`git diff --check` passed for the implementation handoff. No tests, Cargo,
native build, or proof-hole scan ran.

## Preserved candidate and authorship

The exact candidate bytes are retained for a bounded repair attempt:

| Artifact | SHA-256 |
|---|---|
| `YulangClosure/CoreSyntax.lean` | `0250b51b7b97a98e52b76e3785a7341f2b454a422016c6945d7d6c4190804b07ff` |
| `YulangClosure/CoreSubstitution.lean` | `fc73d6d60d28f2abb54049a5715751d27df47ad93dbeb8f52966cf98a747bd2f` |
| `YulangClosure/CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `YulangClosure/ControlSyntax.lean` | `94d9b59e7cc69dac98de9797c7627a571554b859e3906c7c1ca94881d9482864` |
| `YulangClosure/ControlTyping.lean` | `163c191584b6abb462c1e5e190bb2105d6ec3c4f0512568e87570b89ff00ffd8` |
| `YulangClosure/ControlComposition.lean` (unchanged) | `9a48a5f2ef15eb947478757e0fa74457579183ccdbab90f2518886590e33fc40` |
| `YulangClosure/CoreControlBridge.lean` (unchanged) | `30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a` |
| implementation handoff r1 | `3dd4294ddcb16217317289980a0909ee79403420fb3df866968c683a0f213cb1` |
| Proposition A prep handoff r1 | `54e07ff734946435b084389f663a64ae6652df1716d82eef368cbc67527f9ea1` |
| Proposition B prep handoff r1 | `35b63925b8cc383dbcf277cce1905116c23ae86b014b01fd39c5f061387a1fe0` |

All r7 authors are STOPPED. The implementation author changed only the five
new Call representation modules and its handoff. A and B wrote preparation
handoffs only; neither proof module changed. Requested/observed runtime model
metadata and exact elapsed time are UNKNOWN. The full r7 assignment caps remain
charged: implementation 1,800s, A 1,200s, B 1,200s; primary and review each
had 600s reserved. There is no carryover or reclaim.

## Source and proof boundary

The implementation candidate records typed Req/Fail syntax, Call metadata,
actual transition constructors, and a typed literal suffix, but the candidate
is unelaborated. Its reachability and correspondence to the operational source
are not established. In particular, a type containing no `Bad` state would
make a no-`Bad` conclusion vacuous unless the proof connects it to actual Call
execution. The source-order, decorated-plan authenticity, effect-hygiene,
complete observation, frontend/source/native, and arbitrary foreign-tail
obligations remain OPEN. No `BodyLaws` premise or candidate V1–V7 statement is
accepted as evidence.

The exact r7 contract is
`tasks/agent-loop/sprints/lean-complete-call-20261025-r7.md` (SHA-256
`5d0409f5918748fc175e926111710977bb4d0bda6b8a00b4a185b475110e3250`). The
pre-failure baseline was `7262f16cf58f0236a1a140e044d8fbbeb6cf61c6`.
This outcome only preserves the failed candidate and records the obstruction;
it closes no parent or dependent gate.

## Next bounded action

The dispatcher classified r7 as CHECK_FAILED / UNACCEPTED and recommended a
fresh r8 contract. Its first assignment is one Luna/high implementation repair
bounded to 1,200s and the same seven representation paths. It may fix the
listed elaboration issues and resulting errors but may not change semantics; a
required semantic choice returns to Luna. P/Q proof lanes start in parallel
only after the repaired representation is frozen and checked. B starts only
after the exact Proposition A declaration and dependency hash freeze. The
proposed fresh r8 envelope is 6,600s, with no r7 carryover; later assignments
are not yet running. The complete parent remains OPEN.
