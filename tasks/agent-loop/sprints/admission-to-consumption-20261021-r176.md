# R176 — native admission to ordered consumer

Status: **revision 1 prospective-review candidate**. No proof or implementation
worker starts until exact-hash review is CLEAN and Luna activates this contract.

Branch: `research/simple-sub-intrusion`  
Contract revision: 1  
Activation Git HEAD: `e9a7a4fef3d6872fa0596646393a7c0473b3687b`  
Immutable proof baseline: `7ec64a3788175913a2be46331cf0f64c6bd5b407`

Parent theorem:
`notes/theory/2026-10-15-computation-forwarding-preservation.md`, SHA-256
`d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`.
Unchanged fixture:
`tools/inference-playground/examples/r171-formal-name-forwarding.yu`, SHA-256
`cb2fff33a1ab983a932064cc1699d9f4f4a8d5e00d52986525884d42bc58234f`.

R175 is closed `CLOSED_UNFINISHED_RESEARCH`, final review NOT_CLEAN. Its v6
candidate remains frozen and unintegrated. R175 established only successful
physical append/readback for captured bounds; it did not authenticate the
returned admission or later Apply consumer. Preserve its exact frozen results:
implementation/closeout handoff
`tasks/agent-loop/inbox/20261021-r175-implementation.md` SHA-256
`14f6a7b305633d4debb4379c409b812a26c2e43be364ef06e1043d850ca06aca`, proof note
`17ee0f8abd355f8ab69e2622f8605c29d177a5e50b0f4b9829078573de123892`, proof
handoff `91943e16c8f1cf934d5c7d90aee26d5b9e5bcda731f463b2d6ed3d1a12755a39`.

## Immutable source inputs

Luna froze the baseline and R174-v6 source views before review. All files are
mode `0444`, directories `0555`; proof reads these copies, never mutable source.
The newly admitted owner is `candidate_effect.rs`, pinned identically at the
baseline and activation HEAD. `candidate_effect.rs` was read-only discovery
metadata under R175; R176 now proposes it as a proof input, not a write owner.

`/tmp/r176-inputs/baseline-7ec64a378/`:

```text
d884c20a98140da2a737d65f61faa97491bd9a2af7870bf3f0ea7dd428e9ffeb  candidate_context.rs
c1d7ce19ef5192a46d605faabae34e4437b1f1a15819b5657ec1d70eda7900d1  candidate_effect.rs
7c9a46d327a5e2e3f9e6f8d79f36f11fe21b4a3f68426526e85424a39e2c6332  candidate_extrusion.rs
9569e7cc2ba7152cafe1273fba279a8511fe56aa39358798f3e4586c10ede225  candidate_scheme.rs
c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985  lib.rs
153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907  module.rs
13ae8de60293b91e24659090649ff84002f5632a8909451d3f7bd8492b61bea5  shadow_apply.rs
```

`/tmp/r176-inputs/v6-plus-admission-owner/`:

```text
a08ff10637f1ff9a67005f96c5e1bc26a44778f911944054a25cf28bec5ce733  candidate_context.rs
c1d7ce19ef5192a46d605faabae34e4437b1f1a15819b5657ec1d70eda7900d1  candidate_effect.rs
7c9a46d327a5e2e3f9e6f8d79f36f11fe21b4a3f68426526e85424a39e2c6332  candidate_extrusion.rs
48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25  candidate_scheme.rs
24f480355979ee5d96305a08abf6aab67025ede32c2a1575b779e46f5e23b436  lib.rs
153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907  module.rs
2b0e46f28c328172477ac263360f4f3d01d27714dc62cd93235b8e3b1fe4e9ff  shadow_apply.rs
```

The theorem and fixture remain separate read-only pins. These source snapshots
are descriptive evidence, not a new semantic authority.

## Fixed outcome and scope

Constructively follow the original unchanged obligation from authentic source
bound through native admission to actual use:

`source bound → selected seed/owner cause → candidate_bound_origin_with_evidence
→ scoped relation/capture registration → physical FreshUse restoration and
readback → same provider's later Apply → both ordered Replay inputs → actual
consumed FunctionPorts and reused/current-pair discharge`.

Prove correspondence against baseline execution for successful, failed,
retried, duplicate, canonical/self-pair, reused/current and zero-product cases.
Preserve provider identity, alternatives, residual/scoped payloads, shared
anchors, invocation ordinals, both ordered parents and all consumed ports.
Apply any lemma to the original theorem with its source domain, shared xi, open
incoming E, arbitrary finite chains/prefixes, repeated/simultaneous receiving
entries, independent protections and pending/raw-continuation cases unchanged.
A first precise absent constructor is useful unfinished research.

In parallel, inspect resource erasure after the admission owner is understood.
The successful append/readback result does not establish that optional evidence
has no effect on projected traces, diagnostics, resource decisions, publication,
allocation failure or unwind. Do not use field-size subtraction, byte-tally
agreement, endpoint matching or either-parent ancestry as a proof.

## Lanes

**Constructive proof — Sol/high, 1800s.** Read only the immutable seven-file
baseline and v6 source roots, parent theorem, fixture, R175 frozen note/handoffs
and this reviewed authority. Establish the authentic admission/capture owner
and continue the same-provider path through both ordered Replay parents and
actual port discharge, or report the earliest precise missing constructor.
Analyze the resource criterion with explicit vector layouts/capacities, Arc
identity clone, allocator, failed admissions, rollback and unwind. Preserve
all original quantifiers and gates; do not certify implementation.

**Implementation — Luna/high, 1080s.** Inspect the newly pinned admission owner
and existing consumer owners; produce a construction-order design and resource
interference analysis. Current source status is **NO_SAFE_CODE_SLICE**. Exact
code writes remain conditional on the reviewed admission design and an
identified source-supported correction. If activated, Luna may write only
`lib.rs`, `candidate_context.rs`, `candidate_scheme.rs`, `shadow_apply.rs`, the
implementation handoff, this contract for primary-owned sequential revisions,
and `current.json`. `candidate_effect.rs`, `candidate_extrusion.rs` and HIR
`module.rs` are read-only. Any added code owner requires prospective exact-hash
review and a lease/conflict check. Do not change semantics, tests, expected
outputs or the fixture.

The lanes may work concurrently on frozen inputs and disjoint outputs. After
Luna stops source writes, freeze a separate candidate manifest. Proof then
applies to those exact bytes and stops before Luna resumes code writing.

## Exact leases

Luna writes only:

- `crates/yu-solver/src/lib.rs`
- `crates/yu-solver/src/candidate_context.rs`
- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `tasks/agent-loop/inbox/20261021-r176-implementation.md`
- `tasks/agent-loop/current.json`
- this contract for primary-owned sequential revisions only.

The proof worker writes only:

- `notes/theory/2026-10-21-r176-admission-consumption.md`
- `tasks/agent-loop/inbox/20261021-r176-proof.md`

All other paths are read-only. No staging, stash, cleanup, tests, builds, probe,
Yulang2/evaluator run, network, nested CLI, background service or semantic
promotion is authorized. R174/R175 candidates remain unintegrated. All parent,
A/B, source/native and production gates remain OPEN.

## Resources and gates

Fresh cap **4200 seconds**, Astra 0, no carryover. Preparation/snapshot/revision
360s; a 120s prospective exact-hash review is issued separately. No proof or
implementation worker before CLEAN review and Luna activation. After review:
proof 1800, conditional implementation 1080, final proof/code review 480,
one justified delta-review reserve 120, closeout 240: **3720s**. Reviews issue
sequentially. No probe budget. Any future probe needs a new dispatcher decision,
complete discriminating chain, exact command/output review and separate budget;
current status is `NOT_RUN`.

Prospective review checks exact hashes and modes, immutable read-before-write,
source-owner scope, disjoint leases, theorem quantifiers and budget. Final
independent review checks admission, consumers, baseline simulation relation,
resource interference and the exact candidate. Unfinished proof or green finite
instance does not authorize integration. At close record exact hashes, review
receipts, worker/runtime stop observations, charged/expired seconds, open owners
and the next dispatcher boundary. Only Luna may integrate CLEAN exact paths.
