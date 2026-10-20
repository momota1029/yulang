# R182 — same-use caller to consumer correspondence

Status: prospective-review candidate. The proof lane begins only after a CLEAN
exact-pin review and explicit Luna activation. Branch `research/simple-sub-intrusion`;
proposed HEAD `0c260fad5`. Fresh cap 3000s; no carryover from R181. R181 closed
CLEAN for scoped unfinished research and was pushed in `0c260fad5`. The original
forwarding theorem and all parent, A/B, source/native, implementation and
production gates remain OPEN.

Parent: `notes/theory/2026-10-15-computation-forwarding-preservation.md`, SHA-256
`d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`; unchanged
fixture `tools/inference-playground/examples/r171-formal-name-forwarding.yu`,
SHA-256 `cb2fff33a1ab983a932064cc1699d9f4f4a8d5e00d52986525884d42bc58234f`.
R181 contract `b61d1cc8b0efbd480dd964e52f4fd7e083d1ab9a973d7b1ed91af4956ecf3577`,
proof note `d345216984a307a6ab1bc1d94e8f3a951411d1f3973dcc52d503b9bcdc201a16`,
proof handoff `32215df827e5b07cfd78410231d571402336dd7f758e3db681148971a2b3a929`,
and Luna handoff `548fc5f536a104762aab0c4cc33808f693f512c7fd7cd7e49ab71f3a5d12f972`.
Reuse the R178 registration result at note
`notes/theory/2026-10-21-r178-registration-and-consumer-invariant.md`, SHA-256
`c59a06abb002ba76b5b76887edcebb89f7398a99eb3d1ffe6d8787d3908d0291`.

## Fixed outcome

Establish the actual same-source/use correspondence from retained source Apply
and formal/provider construction through admission, both authentic ordered
Replay inputs, FunctionPort/allowance checks and the matching semantic consumer
outcome; otherwise identify the first missing constructor law and its owner.
Apply each established step to the unchanged original theorem's §6
instance-relative implication. Keep shared xi, open incoming E, arbitrary finite
chains and prefixes, repeated/simultaneous entries, independent protections,
pending/raw continuations, alternatives, residual/scoped payloads, current/reused
pairs and valid rollback intact. Preserve parent quantifiers and accepted
source/native behavior. A construction inventory, endpoint equality, observer
flag, `discharged`, queued Support or `Ok` is not semantic acceptance. Retained
Conflict and actual diagnostic outcomes remain explicit in the relation.

## Exact immutable source inputs

Eight pairs are the R181 frozen manifest, with the same roots and pins:

| Owner | Baseline SHA-256 | Candidate SHA-256 |
|---|---|---|
| `candidate_context.rs` | `d884c20a98140da2a737d65f61faa97491bd9a2af7870bf3f0ea7dd428e9ffeb` | `a08ff10637f1ff9a67005f96c5e1bc26a44778f911944054a25cf28bec5ce733` |
| `candidate_effect.rs` | `c1d7ce19ef5192a46d605faabae34e4437b1f1a15819b5657ec1d70eda7900d1` | same |
| `candidate_extrusion.rs` | `7c9a46d327a5e2e3f9e6f8d79f36f11fe21b4a3f68426526e85424a39e2c6332` | same |
| `candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` | same |
| `candidate_scheme.rs` | `9569e7cc2ba7152cafe1273fba279a8511fe56aa39358798f3e4586c10ede225` | `48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25` |
| `lib.rs` | `c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985` | `24f480355979ee5d96305a08abf6aab67025ede32c2a1575b779e46f5e23b436` |
| `candidate_scope.rs` | `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a` | same |
| `shadow_apply.rs` | `13ae8de60293b91e24659090649ff84002f5632a8909451d3f7bd8492b61bea5` | `2b0e46f28c328172477ac263360f4f3d01d27714dc62cd93235b8e3b1fe4e9ff` |

Add only these two R178 owner pairs:

| Owner | Baseline SHA-256 | Candidate SHA-256 |
|---|---|---|
| `candidate_call.rs` | `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479` | same |
| `candidate_source.rs` | `cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7` | same |

All ten pairs use only
`/tmp/r178-inputs/baseline-7ec64a378/` and
`/tmp/r178-inputs/candidate-e9a7a4f/`, except the R181 `candidate_scope.rs`
pair, which uses `/tmp/r181-inputs/baseline-a8f7c4d74/` and
`/tmp/r181-inputs/candidate-a8f7c4d74/`. Prospective review must verify every
source hash, all source files mode `0444`, all four roots mode `0555`, plus all
direct artifact pins. The mutable checkout is not a source input.

**Preparation disclosure:** before this candidate was created, Luna ran a
read-only `rg` over the mutable checkout copies of `candidate_call.rs` and
`candidate_source.rs` while locating the R182 seam. Those paths were clean
relative to `HEAD`; immutable R178 snapshots have the independently recorded
matching hashes above. No claim or proof result relies on that preliminary
search. The prospective reviewer must independently verify the exact snapshots
and decide whether this disclosure affects activation. No other mutable source
inspection, execution, test, build or probe is authorized by this contract.

## Lanes, review and budget

After prospective CLEAN and explicit activation, Sol/high proof owns only
`notes/theory/2026-10-21-r182-same-use-caller-consumer.md` and
`tasks/agent-loop/inbox/20261021-r182-proof.md` (1380s). Luna/high mapping owns
only `tasks/agent-loop/inbox/20261021-r182-implementation.md`, sequential
contract revisions and `tasks/agent-loop/current.json` (600s). Luna remains sole
Git integrator. No compiler edit, test/build/probe, compiler/evaluator/Yulang2
execution, network, nested CLI or scratch authority is granted. Unknown elapsed
charges the full grant; unused reservation expires.

| Work | Seconds |
|---|---:|
| Preparation | 240 |
| Proof | 1380 |
| Luna mapping | 600 |
| Prospective review | 120 |
| Final independent review | 300 |
| Conditional delta review | 120 |
| Closeout | 240 |
| **Total** | **3000** |

Independent falsifiers: sibling/foreign use supplies the consumer; either
Replay input lacks authentic lineage; a pending child/check disappears; a
retained Conflict or `Ok` is misreported as compatible completion; or an
unsupplied inventory entry is promoted to a provider. Final reviewer checks the
whole frozen path, exact pins, and parent quantifiers. A newly required owner or
code-ready seam returns to Luna for a new dispatch. No source-qualified
counterexample, theorem closure or production change is presumed.
