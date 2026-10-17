# Frozen handoff: Operation-to-Catch response instance correspondence

- Assignment: `OPERATION-CATCH-RESPONSE-INSTANCE-CORRESPONDENCE-20261017`, rev1.
- Sprint contract rev2 SHA-256 `88d4d24eff0fd69054643ff86176fc75abcd04d403256b80de8951276e7ea74a`.
- Baseline/checkpoint `e71b38928`; Luna primary, exact two-path lease.
- Artifact: `notes/theory/2026-10-17-operation-catch-response-instance-correspondence.md`.
- Claim class: static source/native correspondence map; no implementation,
  semantic adoption, source acceptance, theorem closure or production result.

## Outcome

The same resolved `SourceOperationDeclaration` structurally feeds both the
Operation expression action and Catch operation-pattern action. Operation
value generation and Catch continuation generation allocate separate local
value/effect/view maps. Slots 42 and 62/63 establish partial endpoint links;
64/65 carry the provisional entry/full-scrutinee effect bounds. The continuation
result is linked to the original scrutinee result, keeping B distinct from S's
answer.

Runtime keeps declaration/payload/event/observations/suffix on `PendingRequest`
and declaration/original-event/suffix on supported `ResumeTemplate` capture.
`ResumeArgument` checks primitive response shape. The fixed Function-response
case refuses before capture/pop; it has no reached consumer.

First missing join: an explicit same-use substitution/instance witness that
relates static signature variables, Catch response ports and the dynamic
request/resume lineage while transporting complete dependent observations,
worlds, profiles and future interfaces. Existing identities/endpoints do not
supply the original `D_B/P_B` or all-response membership. This is a bounded
absence finding, not proof of global absence or a compiler defect.

The artifact does not rely on the concurrent proof proposal. It leaves
`OPRESP-DEFAULT-1`, `OPRESP-DOMAIN-1`, checked `d_B`, original A/B, F1/FK1,
`M_exit`, source/native, implementation and production gates OPEN.

## Integrity and stop

The contract's 22 direct dependency pins matched at lane start. This audit used
static source reading and SHA-256 only: no tests, builds, runtime, probes, code,
expected-output changes, or Git. Only this artifact and handoff were written;
no descendants or scratch paths.

Resource cap: 300 seconds. Conservatively charge **300/300** because the primary did not capture exact active-work start/stop time; this is an allocation charge, not a claim of 300 measured seconds. Stop observed by Luna at 2026-10-17 06:45:55 UTC.

**Writer STOPPED.** Both files are frozen at revision 1. Luna's independent
compiler/spec/architect reviews and integration remain pending. Artifact hash is
recorded in the primary intake receipt after final SHA-256 verification.
