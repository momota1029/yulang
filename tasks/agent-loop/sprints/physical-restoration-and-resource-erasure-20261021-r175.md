# R175 — physical restoration, ordered forwarding consumer, and resource erasure

Status: **revision 1 prospective-review candidate**. No proof or implementation
worker lease starts until exact-hash review is CLEAN and Luna adopts it.

Branch: `research/simple-sub-intrusion`  
Contract revision: 1  
Git activation HEAD: `e9a7a4fef3d6872fa0596646393a7c0473b3687b`  
Immutable proof baseline: `7ec64a3788175913a2be46331cf0f64c6bd5b407`

Parent theorem:
`notes/theory/2026-10-15-computation-forwarding-preservation.md`, SHA-256
`d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`.
Unchanged source fixture:
`tools/inference-playground/examples/r171-formal-name-forwarding.yu`, SHA-256
`cb2fff33a1ab983a932064cc1699d9f4f4a8d5e00d52986525884d42bc58234f`.

R174 closed `CLOSED_UNFINISHED_RESEARCH`, NOT_CLEAN. Its v6 is a frozen,
unintegrated candidate. Independent review accepted only the local completion
frontier repair under ordinary clone/valid-checkpoint hypotheses. Global
resource/allocator noninterference and the provider-to-Apply bridge remain
OPEN. Preserve R174's exact reports in `current.json` and
`tasks/agent-loop/inbox/20261021-r174-implementation.md`; do not infer a proof
from its successful static checks.

Exact R174 evidence pins: proof note
`notes/theory/2026-10-21-r174-rollback-and-forwarding-bridge.md` SHA-256
`45c9d88653d54f018621525e2318a655fec6425727ff484a33375ccd5062689c`; proof
handoff `tasks/agent-loop/inbox/20261021-r174-proof.md` SHA-256
`d874ae111895ce985e780115e02cca4eb64bcb16f99c1788ac156e69c85cfd2a`;
implementation closeout handoff SHA-256
`83b30531a049fb7f6578dc30ef2a2a91fa3d76d55a970ed26f1fa1407e39eb99`.

## Immutable source inputs

Luna froze these copies before review or workers. Files are mode 0444 and their
directories 0555. Proof reads these snapshots, never the mutable checkout.

`/tmp/r175-inputs/baseline-7ec64a378/`:

```text
c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985  lib.rs
d884c20a98140da2a737d65f61faa97491bd9a2af7870bf3f0ea7dd428e9ffeb  candidate_context.rs
9569e7cc2ba7152cafe1273fba279a8511fe56aa39358798f3e4586c10ede225  candidate_scheme.rs
13ae8de60293b91e24659090649ff84002f5632a8909451d3f7bd8492b61bea5  shadow_apply.rs
7c9a46d327a5e2e3f9e6f8d79f36f11fe21b4a3f68426526e85424a39e2c6332  candidate_extrusion.rs
153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907  module.rs
```

`/tmp/r175-inputs/r174-v6-plus-restoration-owner/`:

```text
24f480355979ee5d96305a08abf6aab67025ede32c2a1575b779e46f5e23b436  lib.rs
a08ff10637f1ff9a67005f96c5e1bc26a44778f911944054a25cf28bec5ce733  candidate_context.rs
48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25  candidate_scheme.rs
2b0e46f28c328172477ac263360f4f3d01d27714dc62cd93235b8e3b1fe4e9ff  shadow_apply.rs
7c9a46d327a5e2e3f9e6f8d79f36f11fe21b4a3f68426526e85424a39e2c6332  candidate_extrusion.rs
153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907  module.rs
```

The R171 fixture and parent theorem remain separate read-only pins. The HIR
module file is included solely to inspect receipt identity Clone owners. These
are exact source inputs, not adopted semantic authorities.

## Fixed outcome and scope

Constructively establish the same provider's full path:

`source Fact/Cause → selected seed → provider Capture/source bound → own
FreshUse map → actual restoration operation → physical admission/readback →
callee lower fiber → actual forwarding Apply demand → both ordered Replay
inputs → consumed FunctionPorts`.

Preserve every route, shared anchor, canonical self-pair, residual/scoped
payload, invocation ordinal, finite prefix and failure/retry path. Apply useful
lemmas to the unchanged parent theorem, retaining its domain, quantifiers,
shared satisfying assignment, open incoming E, arbitrary finite chains and
repeated calls. A precise first absent constructor is useful unfinished
research, not theorem closure.

In parallel, replace R174's estimated `size_of(field)` subtraction and
untracked completion vector with a source-supported accounting design. Show
that optional evidence allocation, identities/clones, rollback, capacity
changes, publication, Result failures and unwind cannot alter projected solver
traces, diagnostics or resource decisions. Missing evidence must remain
unavailable without a semantic error. Do not use host-layout assumptions as a
proof and do not remove the failed Capture-membership predicate to force a
positive result.

## Lanes

**Constructive proof — Sol/high, 1500s.** Read only the frozen six-file
baseline and R174-v6 input roots, theorem, fixture, R174 frozen note/handoffs,
and exact reviewed authority. Establish physical restoration, its actual
admission/readback consumer, both ordered Apply Replay inputs and consumed
ports, or identify the first missing owner. Prove a source-level erasure
criterion including capacity and clone owners. Apply results to the original
theorem and report exact remaining premises. No implementation certification.

**Implementation — Luna/high, 1380s.** Work only in `lib.rs`,
`candidate_context.rs`, `candidate_scheme.rs`, `shadow_apply.rs`, and the R175
implementation handoff. `candidate_extrusion.rs` and `crates/yu-hir/src/module.rs`
are read-only inputs initially; any new write owner requires a reviewed exact
delta and conflict check. Prefer owner indices or already-retained identity
tokens over new owned Cause/occurrence clones. Keep actual layout and capacity
accounting explicit. Replace the impossible temporal join only with the real
producer-consumer chain. Stop at the first unsupported link.

The lanes may work concurrently on immutable baseline/v6 snapshots and
disjoint outputs. After Luna stops code writes, she freezes a separate R175
candidate manifest. The proof lane then applies its result to those exact
candidate hashes and stops. Luna makes no solver writes until that proof stage
stops. This ordered seam is pre-authorized by this contract.

## Exact leases

Luna writes only:

- `crates/yu-solver/src/lib.rs`
- `crates/yu-solver/src/candidate_context.rs`
- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `tasks/agent-loop/inbox/20261021-r175-implementation.md`
- `tasks/agent-loop/current.json`
- this contract for primary-owned sequential revisions only.

The proof worker writes only:

- `notes/theory/2026-10-21-r175-physical-restoration-and-erasure.md`
- `tasks/agent-loop/inbox/20261021-r175-proof.md`

All other paths, snapshots, source fixture, theorem and unrelated dirty files
are read-only. No staging, stash, cleanup, build, test, Yulang2/evaluator run,
network, nested CLI, background service or probe is authorized. R174 remains
unintegrated. All parent/A/B/production gates remain OPEN.

## Resources and gates

Fresh cap **4200 seconds**, Astra 0, no carryover. Snapshot/revision preparation
360s is charged. A 120s prospective exact-hash review is issued separately;
no proof/implementation worker before CLEAN review and Luna activation.

After prospective review, remaining allocations are proof 1500, implementation
1380, final proof/code review 480, one conditional delta review reserve 120,
closeout 240: **3720s**. Review grants are issued sequentially. No probe budget
is allocated. Any future probe requires a new dispatcher recommendation, exact
input/command/output review and complete discriminating bridge; current status
is `NOT_RUN`.

The prospective reviewer checks exact hashes, immutable read-before-write,
source-owner expansion, disjoint leases, outcome/quantifier preservation and
arithmetic. Final independent review must check the full resource/clone/rollback
proof and actual ordered bridge on a frozen candidate. An unfinished proof or
green finite instance cannot authorize integration.

At close record hashes, review receipts, stop/runtime/elapsed observations,
charged and expired seconds, unclosed owners, parent premises and the next
dispatcher boundary. Only Luna may integrate a CLEAN reviewed exact path set.
