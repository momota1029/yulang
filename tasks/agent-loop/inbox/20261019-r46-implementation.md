# R46 implementation/source-native handoff — revision 1

Sprint/contract: `source-apply-owner-20261019-r46`, rev2, SHA-256
`d7d7e1cf123bce1b51eec1bd599f47faac75aa7b75d41f9a1a7030440855ef62`.
Baseline: pushed commit `55ed588e7`; source bytes and primary-owned overlay
hashes are pinned in the contract.

Role: Luna primary, read-only source/native map. Requested Luna/high;
runtime-observed model/effort UNKNOWN. Exact outputs:

- `notes/progress/2026-10-19-r46-source-native-owner-map.md`, SHA-256
  `f94e6e0e576d3ec5e73316f89a4a7b93dceb88b328f21a0516b9d39f8dff4d99`.
- This handoff, SHA-256 recorded after freeze.

## Outcome class and parent application

The source/native path has an occurrence-specific candidate chain from HIR
Apply through `ApplySourceInput`, a generated Apply relation, native Function
demand ports, and typed Function result/result-effect consumers. Exact field
and provenance checks are recorded in the map. This is partial candidate
source/native evidence only. It does not derive the original source typing
judgment, an authentic Application output `Desc`, or its ordered free
dependency telescope `D_q`.

Parent: unchanged inference/evaluator theorem and Simple-sub A/B remain OPEN,
0 → 0. R45's bounded obstruction stands within its pinned envelope. The first
missing premise still belongs to authoritative Application result-description
formation at q, before downstream Call, frame or alias construction.

## Source → generated relation → typed consumer

The map traces the same retained Apply occurrence into source registration,
then checks recipe/source occurrence and endpoint agreement before admission.
The native demand stores distinct argument, argument effect, invocation effect,
result, and application effect. The invocation effect is distinct from the
whole Apply effect. Backward from a typed Function comparison, the operational
Function dispatch exposes typed argument, argument-effect, result-effect and
result pairs; Result and ResultEffect use Preserve. Those links retain typed
consumer identity and do not introduce source Description metadata or `D_q`.

The ordinary local-recursion path also has an authentication seam: scoped
Apply admission requires a retained LocalFreshRoute for a local-name callee,
while local names found in active initializers are emitted as Action::Link.
Whether the exact q call takes this path and the resulting gate consequence
remain under independent source/proof review. No source failure or runtime
rejection is claimed.

## Checks, omissions, resources, status

No tests, build, Cargo, runtime probe, expected-output edit, or semantic change
was authorized or run. Static inspection only. Full source Call arms,
provider/future/receiver/return/pending/W/Z derivations, two independent frames,
shared alias, and evaluator theorem remain open. No code slice is authorized.

Luna's 600-second read-only mapping grant is charged/reserved; actual elapsed
CPU/RSS are UNKNOWN. Current exact output writes are complete pending freeze;
after hashing this handoff, primary writes stop for independent review.
Implementation gate: NO_SAFE_CODE_SLICE. Commit readiness awaits the R46
proof result, two independent reviews, and Luna adjudication.
