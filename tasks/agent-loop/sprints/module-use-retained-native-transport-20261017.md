# Sprint: `module-use-retained-native-transport-20261017`

Status: READY FOR CANDIDATE IMPLEMENTATION
Revision: 1
Baseline: `9f8a03bdf`
Parent: original Yulang inference/execution theorem; source domain, admissions,
observations, original A/B claims and quantifiers remain unchanged.

## One outcome

Retain the actual module-use `FreshUse` crosswalk for the lifetime of each
committed candidate module route, and prove ownership, accounting, rollback and
drop behavior from the frozen implementation. Apply this result only to the
native field-map contract's remap-retention premise. It does not supply
source-field ownership, classify a handle, construct total `Phi_u`, or close an
original theorem condition.

## Lanes and exact leases

1. `implementer` (Luna/high), maximum 480 seconds, owns only:
   - `crates/yu-solver/src/candidate_scheme.rs`
   - `tasks/agent-loop/inbox/20261017-module-use-retained-native-transport-implementation.md`

   Retain the existing module route's actual Graph and complete non-row
   `FreshUse` remaps through commit until route rollback/session destruction.
   Reuse private `RetainedFreshUseMaps`/`into_retained_parts` where sound; keep
   existing API signatures and avoid public certificate or semantic-classifier
   surfaces. Prove checked capacity accounting counts every backing allocation
   exactly once, with transition scratch separated from retained bytes. Preserve
   existing availability/error handling and private construction/publication
   boundaries. Do not change candidate admission, rule selection, diagnostics,
   fixtures, expected outputs, source grammar or compiler meaning.

2. After implementation STOP and frozen hashes, `prover` may use at most 300
   seconds and owns only:
   - `notes/theory/2026-10-17-module-use-retained-native-transport.md`
   - `tasks/agent-loop/inbox/20261017-module-use-retained-native-transport-proof.md`

   Prove actual module route ownership, lifetime, all remap components,
   retained-capacity identity, checked accounting, rollback and destruction from
   frozen bytes. Apply only the remap-retention premise. Keep source field
   completeness, handle class, native/source adequacy and `Phi_u` explicitly
   open.

3. After author STOP, independent read-only review is sequential:
   compiler/source 180 seconds; architecture/resource 180 seconds; exact spec
   conformance 120 seconds. Each reviewer checks the exact frozen code and proof
   hashes and stops before another reviewer starts.

4. Luna-owned focused verification, at most 180 seconds, runs only after code
   freeze: `cargo check -p yu-solver --features shadow-apply-candidate --tests`
   and the single focused regression test added for module-route remap retention
   (record the exact filter in the handoff). No benchmark campaign or concurrent
   heavy process. If the focused command cannot finish within its envelope,
   report it accurately without retrying or promoting static evidence.

Fresh cap 1800 seconds: implementation480 + proof300 + compiler180 +
architect180 + spec120 + focused verification180 + coordination120 + reserve240.
No author overlap; proof starts only after implementation and checks are frozen.

## Complexity and failure boundary

The user explicitly authorizes computational-complexity changes. The design may
retain additional finite crosswalk storage and use more work to preserve it.
Record proposed and measured/verified costs separately. Count nested payloads,
dependency/remap records, route headers and vector/hash capacities; distinguish
retained payload from transition scratch and existing graph/session storage.
Do not claim physical allocator bytes or asymptotic improvement without evidence.

No new source rejection, successful certificate, retry policy or diagnostic is
selected. Failed reservation/checked arithmetic continues through the existing
availability path; no partially built route is published. If exact accounting
cannot be maintained without changing admission or observable behavior, stop
and return the concrete delta for review.

## Fixed dependencies and boundary

- Preserve native field-map revision 2 as a readiness contract only.
- Preserve the independently CLEAN handle-boundary proof: `HINTRO-OWNER-u_id`
  remains open; no Published/Mono branch is selected.
- Reuse the existing local-use route's retained-map ownership only as an
  implementation pattern, not as semantic authority for module routes.
- Keep module `FreshRoute`, `LocalFreshRoute`, Graph/session owners and rollback
  journals distinct where their current lifetime differs.
- Three inherited UNKNOWN reservations remain quarantined. The historical
  implementation resident had no assigned code/output lease; verify exact
  paths and active runtime before dispatch. Do not reclaim or overlap unknown
  writers.
- No total source/native map, source `Sig`/field-key ownership, source
  handle-owner rule, root/Call construction, F1/FK1, N-Transport, soundness,
  principality or termination closure is implied.

## Frozen inputs

```text
crates/yu-solver/src/candidate_scheme.rs 52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a
crates/yu-solver/src/candidate_source.rs efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38
crates/yu-solver/src/lib.rs 2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f
notes/design/2026-10-17-module-native-field-map-contract.md 1465b65979b2742de020c2bc7b44ff6fb53adefa7158d9fa3947d0b4d5923502
notes/theory/2026-10-17-module-source-handle-introduction.md df0e684bad2da05741e39db12bd06bb400ad8b5b15af4116abab4df6c9df06c3
tasks/agent-loop/inbox/20261017-module-source-handle-introduction.md 46412c131659b8cd9621e38053dcce49916087788c9c90c5442bef51db84f4d2
tasks/agent-loop/inbox/20261017-local-use-retention-applied-correspondence.md edec4fc3252351f62235ed7caaed6844c720d17e6a3805fb9f9fa9dd310e7fa4
tasks/agent-loop/inbox/20261017-local-use-retention-implementation.md e78fd6cee9c1afeac740158b45084647dc495b963ddbafaad00f9f8f26b9b009
notes/theory/2026-10-17-local-use-existing-map-retention.md f214960d2e1ac04f361a01f0802539ea9c961099fc9b55faa93d023f8cabac2e
```

## STOP and closeout

Stop on any pin mismatch, active/conflicting code writer, unexpected caller or
API change, accounting omission, partial publication, source-observable change,
or need for unleased files. Preserve the original quantifiers and domain.

At sprint end report only: original theorem conditions genuinely closed;
implementation/test behavior newly established; and what remains unproved plus
the next single condition to attack.
