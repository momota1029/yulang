# Sprint choice-a-root-source-key-contract-repair-20261017

Status: ACTIVE, Luna-admitted at baseline `768476b933118fa6e0912e620addc9c6a2ee3a4c`.
Branch: `research/simple-sub-intrusion`; contract revision: 1.

## Parent and outcome

Parent remains the original Yulang inference/execution goal with original A/B
claims, quantifiers, source/native correspondence and all F1/FK1, N-Transport,
Call, soundness, principality, termination and production gates OPEN.
Predecessor repair sprint `choice-a-carrier-and-diagnostic-contract-repair-20261017`
closes REVIEWED-PARTIAL after its fresh spec reviewer closed both previous
MAJOR findings and identified one new root-source-key mapping inconsistency.
No original theorem condition closes.

Outcome: repair the exact direction-A successor contract and establish static
implementation feasibility for source-key mapping of a preserved body-root
occurrence that old ordinary lowering left unmapped. Then obtain fresh sequential
spec, compiler and architecture reviews. Reuse the frozen source audit and all
existing implementation pins. Direction A permits this proposal repair/review;
no code/test authority exists, and exact final user approval remains necessary.

## Exact inputs

Baseline: `768476b933118fa6e0912e620addc9c6a2ee3a4c`.
Current successor revision 2 SHA-256:
`9773bfe7631ccf2325435177c0a438cc637ca404bfb3b5863b7a827018d14c24`.
Its handoff revision 2 SHA-256:
`5aa27034165a3d02e9de2fdd969b29c70f4ebed99e80c5edd31de3634f04ff05`.
Both are preserved byte-for-byte under `tasks/agent-loop/archive/` before
successor revision 3 writes.

Frozen source/CST audit SHA-256:
`e8a320be0e78ecc2c5ee5210338476740c03a1fae61fb2747ec39636286ad501`.
Direct source pins:

```text
crates/yu-hir/src/module.rs 2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e
crates/yu-hir/src/module/local_source.rs ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5
crates/yu-hir/src/source_identity.rs aa97bc34be51644cf944b2813af47ad9243a8eb270850eeb6df34b9cddb3b3a2
```

## Repair and feasibility requirements

1. Preserve the allocated body-root occurrence ID while registering its exact
   outer application `MlArgument`/`CallTail` source key.
2. Stage mapping additions both for a previously unmapped retained body-root
   occurrence and for newly allocated canonical-HIR descendants.
3. Preserve every existing mapping. If a root occurrence already maps to the
   exact same key, retain it without duplicate insertion. If it maps to a
   different key, fail explicitly as inconsistent identity; never overwrite.
4. Preserve ordinary carrier formation/results, old carrier IDs and ordinals,
   and distinct canonical-HIR/carrier occurrence IDs that can map to the same
   parse key.
5. Specify checked reservations, atomic mapping publication and failure
   disposition. Do not use `record_occurrence`'s overwriting insertion as proof
   of safe collision handling.
6. Add future regression obligations for the retained root ID's previously
   absent mapping, exact Application key, descendant keys, and carrier
   noninterference.
7. Static feasibility trace (read-only): follow unsupported `lower_body` early
   return; `lower_leaf`'s mapping behavior; `HirSourceIdentity::append_stage`
   duplicate-ID rejection; and `form_ordinary`'s staged identity merge. Report
   exactly which current behavior supports the proposed construction and which
   atomic staging/reservation step still requires implementation. No runtime or
   test invocation.

Any incompatible mapping representation or collision behavior remains an open
choice; do not adopt it silently. No new source dependency is expected.

## Roles, leases, resources and sequence

Luna/high author, <=120s, owns exact writes to:

- `notes/design/2026-10-17-ordinary-hir-application-admission-successor.md`
- `tasks/agent-loop/inbox/20261017-ordinary-hir-application-admission-successor.md`
- frozen snapshots of revision 2 under `tasks/agent-loop/archive/` (already
  created before this author turn).

After author STOP and frozen rev3 bytes: fresh sequential spec <=100s, compiler
<=100s (feasibility plus source audit), architect <=100s. Reviewers are read-only
and write no files. No overlap; each reviews the exact same design, handoff,
source audit and direct dependencies. Major findings cannot exceed the 120s
repair author cap; if it is exhausted, stop REVIEWED-PARTIAL with exact residual.

Cap: 600s total: Luna120, reviews300, coordination60 charged to selector,
reserve120. Predecessor sprint's remaining320s is retired; no carryover.
Preserve all three inherited UNKNOWN leases and reservations as quarantined.

## Non-goals and closeout

No source/library/compiler/test edits, tests, builds, Cargo or runtime probes;
no source acceptance, Call typing, solver result, source T, theorem closure,
production promotion or final semantic/API adoption. The repaired contract must
still be presented for explicit user approval after reviews. Report original
theorem conditions closed (0), behavior/test evidence (none), and the next exact
open gate.
