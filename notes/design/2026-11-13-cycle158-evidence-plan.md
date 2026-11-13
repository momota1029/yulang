# Cycle158: current nominal evidence from historical captures

Status: proof plan, 2026-11-13. Targets the V5 evidenceNode gap without changing semantics.

Data: a real reachable tracked state and a packet in its journal; a source-preserving
Refines from its historical context to current context. Syntax scope initially unary
nominal/variable, later finite nested nominal/variable if the inspection induction closes.

Independent judgment: existing RecursiveEvidence.Instance and Evidence, unchanged.
The executable inspector is existing RecursiveInspection.inspect/inspectMany.

Prove current Instance for every current Models assignment from historical packet,
computed syntax/lookup, and Refines. BranchModels is derived, never an input. Actual
current argument lookup, declaration role, RootDefined, and Metadata are explicit
syntactic requirements, not inferred from Stable alone. Then selection coherence fixes
key/children and the existing evidence node rule combines independently given children.

Parallel work proves finite nested inspection transport and compound scalar child
interval formation. Neither changes Astra-owned transition/candidate definitions.
All results retain exact fragment assumptions; general evidenceNode stays open until
coverage, arbitrary inspection, and stability bridges are actually discharged.

Yulang2 role audit Y2-ROLE-003/004 has document-level reexpansion and lower/upper cross
constraints, not an executed nested fixture. Current spec06 and existing inspector are
the authorities; no new runtime compatibility claim.
