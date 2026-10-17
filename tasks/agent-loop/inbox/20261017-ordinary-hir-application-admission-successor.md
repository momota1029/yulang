# Frozen handoff: ordinary-hir-application-admission-successor

Sprint: `choice-a-root-source-key-contract-repair-20261017`, revision 1.
Sprint SHA-256: `9314b4c6acb0948bbd59bd45c0342296fa53043eec7c2b8b82bf8581217bfe69`.
Assignment: `ordinary-hir-application-admission-successor`, handoff revision 3.
Successor artifact revision 3:
`notes/design/2026-10-17-ordinary-hir-application-admission-successor.md`,
SHA-256 `ae572403ec4e36c56f034135f9e223e93dc9f0bad5c01fbed1d368048713eb2a`.
Revision 2 and its handoff are preserved byte-for-byte under
`tasks/agent-loop/archive/` (prior design `9773bfe7631ccf2325435177c0a438cc637ca404bfb3b5863b7a827018d14c24`, handoff `5aa27034165a3d02e9de2fdd969b29c70f4ebed99e80c5edd31de3634f04ff05`).

Parent: original Yulang inference/execution goal; original A/B claims,
quantifiers and source/native obligations unchanged. Original theorem conditions
closed: 0. HIR-APP-CST-1 remains candidate pending compiler review.
HIR-APP-ADMISSION-1 remains OPEN pending fresh review and explicit final user
approval.

Baseline `768476b933118fa6e0912e620addc9c6a2ee3a4c`. Frozen source audit SHA:
`e8a320be0e78ecc2c5ee5210338476740c03a1fae61fb2747ec39636286ad501`.
Direct code pins:

```text
crates/yu-hir/src/module.rs 2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e
crates/yu-hir/src/module/local_source.rs ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5
crates/yu-hir/src/source_identity.rs aa97bc34be51644cf944b2813af47ad9243a8eb270850eeb6df34b9cddb3b3a2
```

Fresh spec review of revision 2 closed the prior ordinary-carrier omission and
dense-ID stability conflicts, then found that an old unsupported application
body root kept its `HirOccurrenceId` but had no source-key entry. Revision 3
requires that preserved ID to map to its exact outer Apply `MlArgument` or
`CallTail` key. It stages this mapping and descendant mappings together; an
existing identical mapping is retained without insertion, a conflicting key
fails as `InconsistentIdentity`, and no existing mapping is overwritten.
Carrier identities remain separate IDs and their old ordinals are preserved.
The contract requires an occurrence-only checked stage merged through
`HirSourceIdentity::append_stage` after carrier formation and before returning
the private module, with no partial publication.

Static feasibility trace completed by Luna against pinned sources (read-only):
ordinary unsupported `lower_body` returns before `lower_leaf` records the body
source mapping; `lower_leaf` maps a resolved leaf through `record_occurrence`,
whose insertion overwrites and is therefore not an acceptable stage primitive;
`HirSourceIdentity::append_stage` rejects duplicate occurrence IDs and reserves
before extending maps; `form_ordinary` takes a private identity stage, forms and
orders carrier occurrences, then merges the stage before module construction.
These owners support the required mapping merge and atomic reservation. They do
not yet stage canonical Apply descendants after carriers: implementation must
hold accepted application projections private, preserve error emission order,
then finalize child occurrences and source mappings after the carrier pass.
That is an implementation step, not executed evidence. No incompatible identity
representation was selected.

Outcome class: successor proposal rev3, not adopted. Role/author Luna `/root`,
requested/effective model UNKNOWN; 120s fully conservatively charged, writer
STOPPED. Exact output leases are design and handoff. No code or tests. Static
checks `python3 tools/agent_sprint.py check` and `git diff --check` passed; no
compiler, build, Cargo, runtime probe or test ran. Three inherited UNKNOWN
leases remain quarantined. Next: sequential fresh spec, compiler (including
feasibility trace and source audit), then architect review of these exact bytes.
