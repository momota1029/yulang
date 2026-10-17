# Closeout: choice-a-carrier-and-diagnostic-contract-repair-20261017

Status: CLOSED-REVIEWED-PARTIAL at baseline `768476b933118fa6e0912e620addc9c6a2ee3a4c`.

Fresh spec review of successor revision 2 closed both predecessor MAJORs:
ordinary `SourceCarrierOutcome` preservation and dense per-product
Error/Diagnostic IDs with downstream numeric shifts. It found one new MAJOR:
the preserved body-root occurrence must acquire its exact Apply source-key
mapping, although revision 2 limited sidecar extensions to new child IDs.
Existing ordinary unsupported lowering returns before `lower_leaf` records the
root mapping.

No compiler or architecture review was started after this material spec blocker.
No source-meaning, identity collision or implementation rule is adopted by the
finding. No code/tests were authorized or run. No original theorem condition
was closed. Revision 2 design and handoff are preserved byte-for-byte in
`tasks/agent-loop/archive/`.

The bounded successor repair and static feasibility packet is
`tasks/agent-loop/sprints/choice-a-root-source-key-contract-repair-20261017.md`.
It reuses existing pins and source audit; 320 seconds from the closed sprint
are retired and cannot carry over.
