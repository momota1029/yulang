# Sprint native-plan-authority-boundary-correction-20261017

Status: frozen by Luna for one bounded correction to a reviewed planning artifact.
Branch / source baseline: `research/simple-sub-intrusion` / compiler baseline
`74bfaa6a8ce0a60051e40e531c54576516d6c151`; current record baseline is
`3df4e0e28`. No compiler source path is in scope.
Authority: adopted NPAIR proposal and adoption receipt; exact review finding in
the preceding native-plan sprint review record in `current.json`.
Contract revision: 1.

## Outcome and boundaries

Repair the one MAJOR finding that an implementation-readiness plan mandates a
native representation even though adopted NPAIR §3 leaves representation
unselected. Preserve the adopted semantic/evidence invariants and all proof
obligations. Explicitly label registries, node types, edge identifiers, maps,
storage ownership, and processing order as unselected implementation options
pending a later architecture decision. Do not weaken actual ingress, complete
dependent transport, consumer, scope, lineage, scheduling or publication
requirements.

No new architecture decision, source semantics, compiler code, tests, expected
output, or production authority. Parent theorem and all mathematical,
source/native, implementation and production gates remain OPEN. The frozen old
artifact and its original handoff/reviews remain unchanged evidence.

## Exact outputs and sequence

Luna first retains exact pre-repair bytes at
`tasks/agent-loop/snapshots/20261017-negative-pair-native-implementation-contract-pre-repair.md`
(SHA-256 `ff91cfa400bbf547b8cfa6a3ddf773eb54e36ca6aabf9023750fd5308b60a8d4`).
Then write the corrected revision 2 at the existing
`notes/design/2026-10-17-negative-pair-native-implementation-contract.md` path
and one new handoff at
`tasks/agent-loop/inbox/20261017-negative-pair-native-plan-authority-repair.md`.
Produce closeout receipt `notes/progress/2026-10-17-adopted-npair-sprint-closeout.md`.

The corrected plan must state the binding evidence invariants separately from
the deferred internal representation choices, consistently across the owner
table, future code sequence and conclusion. Preserve all proof boundaries,
especially J2's conditional status and the bounded Catch receiver experiment's
limited authority. Reviewers receive exact revision 2 artifact, repair
handoff, pre-repair snapshot and this frozen contract. Their review covers the
complete delta and whether any representation has become mandatory or any
semantic obligation was weakened. Review architect first, then spec auditor;
stop on any new major/blocking finding.

## Resources and stop

Fresh 240 seconds, no carryover: Luna wording repair 60; independent architect
delta review 60; independent spec-auditor delta review 60; coordination 30;
reserve 30. Three historical UNKNOWN reservations and quarantined board lease
remain. One author at a time. No Astra, code lease, tests, Cargo, probes or
compiler execution. No descendants. Only Luna stages explicit files, inspects
the full outbound range and pushes non-forced after both delta reviews and
adjudication. Any further semantic/architecture choice or exhausted allocation
ends this correction with the gates open.
