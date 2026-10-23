# CONCRETE-CALLBACK-PERMISSION-20261024 — outcome

Status: **NO_SAFE_CODE_SLICE** for dependent runtime changes. The bounded
callback-result permission obstruction passed fresh independent review. This
closes the sprint's evidence task only; it does not close
`SOURCE-SAFETY-BRIDGE`, prove a compiler defect, or complete the broader
type-inference/evaluator goal.

Contract: `tasks/agent-loop/sprints/concrete-callback-permission-20261024.md`,
SHA-256 `4a6b3a6e10d3c496640c015104d555c115e351dd41806f45c04fe6e20fa24f94`.
Baseline: `5fbc2c2d9e3ab28032caf599ca024b8ba8b19778`.

## Bounded result

Approved policy §§1.1–1.2 selects result `1` for
`relay(cb: () -> [signal] int)` handling the callback's `signal`. The
annotation grants local handling permission and does not close the callback's
input row; additional `write` remains an outward obligation. No execution of
the sample was claimed.

The source constructors retain the permission precisely: the outer function
effects are absent while the result row retains resolved `signal`, its source
row position and origin. Candidate admission creates a negative
`FormalPermission` at structural path `[Result]` over a fresh open effect
port, so this permission is not a closed upper bound. The captured projection
retains the formal, annotation owner, Lambda occurrence, row, path and family.

The runtime path has no corresponding constructor. The relay Lambda is emitted
with Value role and `root_schema=None`: `RootCompSchema` requires outer
effects and does not construct a schema from the nested result row. Value entry
preserves the supplied callback's opaque view and creates no permission
boundary. A later value observation can create a genuine receipt, but that
receipt does not create the missing boundary or callback-result execution view.

The request consumer ordering is decisive. The operation call creates an inert
request carrier; its `ReceiverReturn` ends the operation invocation and
restores the relay owner; only then does `OperationResultConsumer` execute the
carrier and create the request event from currently executing views. A view
covering only the callback callee invocation ends too early. The same relay
Catch requires an active receiver boundary, matching family, authentic
same-event observation, same-view receipt and image reachability. Missing
grant returns `HandlerEvidence`; it proves neither nonprotection nor
forwarding. The closed-primitive certificate rejects the retained Lambda.
No alternate current route supplies the absent callback-result view.

**Adjudication:** `NO_SAFE_CODE_SLICE` under the current contract. No
dependent runtime patch is authorized by a missing-constructor finding. The
next bounded construction must carry authenticated permission from the actual
formal and Result path through the supplied callback's receiving view and the
request-producing consumer, into the same relay Catch. It must preserve event,
view and owner identity, unknown inherited coverage, and the residual
`write`; a sibling invocation, type equality or family spelling cannot grant
it. Any new source owner or write path needs a versioned contract.

## Frozen evidence and independent review

| Artifact | SHA-256 |
|---|---|
| Contract revision 1 | `4a6b3a6e10d3c496640c015104d555c115e351dd41806f45c04fe6e20fa24f94` |
| Proof artifact | `c228ff45a272a52b92eaaccd91183272438bb8c3287dd39e7749d700ce919f4d` |
| Producer inbox | `dddd305fb7d0aa6aca86b0868cf1a4806703e58e57f7c8b8e2e14ac0c5949335` |

Fresh non-contributor `/root/proof_implementation_referee` reviewed the
frozen obstruction and all 15 pinned dependency hashes. Disposition: supported,
with no BLOCKING, major or minor findings and no alternate route or
counterexample. The review confirms only this direct operation-callback
construction gap; it does not certify whole-program source acceptance,
complete `write` residual behavior, arbitrary callbacks, resume, original A/B
or a parent theorem.

The proof producer stopped after 334 instrumented seconds, 81 read-only calls
and three artifact-only patch calls. The reviewer stopped after 66 seconds, 12
read-only calls and two clock calls. Neither ran tests, builds, probes or Git
operations; no descendants remain. Luna independently checked both artifact
hashes and recorded STOPPED receipts. No production code or expected output
changed.

`python3 tools/agent_sprint.py check` passed as static state validation; it is
not proof or runtime evidence. No test or compiler check was run for this
sprint. The source/native parent, original A/B and inference/evaluator goal
remain open.
