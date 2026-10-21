# Native admission and module schedule — R165

Status: candidate sprint following R164 and the user's direction to move onto the checked-out Yulang3 implementation and original inference proof. No implementation command or new worker grant exists until prospective review is CLEAN and Luna issues exact leases. Branch `research/simple-sub-intrusion`; checkout HEAD `09f5108098d55bc09326ace1f05ca6b6aaf667e1`. No Yulang2 binary/archive execution is authorized.

## Original outcome and success evidence

Keep the full user goal: implement natural Simple-sub inference and evaluator behavior with proof, and broaden unchanged Yulang2 Web example execution. This sprint advances two independent parts:

1. **Original proof gate:** prove or produce a precise source-qualified obstruction for native mapped-bound admission in the original computation-forwarding preservation obligation, applying reviewed R70/R71 conditional results without changing their hypotheses or the parent quantifiers.
2. **Checked-out evaluator:** correct the source-schedule constructor's omitted `Case` form only if an independent source review confirms that the existing classifier's established meaning is “may be a computation root.” Preserve source order and selected-definition behavior. This is one actual evaluator improvement; it does not claim complete whole-module or imported-library execution.

Observable progress is an original-premise discharge or exact falsifier for lane 1, and an exact source-level classification repair plus successful workspace-package typecheck for lane 2. A note count, selected-`main` success, or test count is not success. All Simple-sub/evaluator A/B, complete source/native, accepted-inference, Y2 Types/Console, import, tuple, primitive, host-write and production gates remain OPEN unless directly discharged by reviewed evidence.

## Frozen authority and dependencies

- Approved inference principles: `notes/design/2026-10-11-yulang-inference-top-level-principles.md`.
- Original forwarding parent: `notes/theory/2026-10-15-computation-forwarding-preservation.md`, SHA-256 `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`.
- R70 contract `4fa363c4dcbd97450b16dd2afb8b1bf2889f9faf00168d444205fe3633bee5cf`; reviewed result note `648b594fdf1cd989e7399db00f396c65ec82cc1b4d3585bcb68ce21b316021e7`.
- R71 contract `a6bd6aa1ab369f77b728014cd51693b11c5b3f97f85aab392d6488c8834ac1fb`; reviewed result note `620947cece53ca60a7f8a2388a398f53850b835c79afd546bfdcfd10349a876e`.
- Provisionally adopted R149 behavior: `notes/theory/2026-10-20-r149-types-console.md`, SHA-256 `d57681689e4d8b487c9fb749db675ebf1ae5cb008cea47085503208482534861`; proof map SHA-256 `6f9a7a430f54fe412163ddec7f374ff9a671d7d5ec62fa6cec252e8cb7800828`.
- Current exact source SHA-256 pins at checkout HEAD:
  - `crates/yu-solver/src/candidate_scheme.rs`: `2e64dc8781189b4da21c30f4d1b3208aaef48ca247cae55fb7e77e68b5857850`
  - `candidate_extrusion.rs`: `7c9a46d327a5e2e3f9e6f8d79f36f11fe21b4a3f68426526e85424a39e2c6332`
  - `candidate_intrusion.rs`: `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97`
  - `candidate_context.rs`: `93ff11f005c9e29e007d2a21479779dd14ff462a41da9c937a0e6a48fc1603be`
  - `crates/yu-solver/src/lib.rs`: `c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985`
  - `tools/inference-playground/src/runtime/program.rs`: `28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d`
  - `tools/inference-playground/src/runtime/machine.rs`: `4fb918732047f61184bc8f89b829bde68a8d1e6649a24d02640ec14500ae0acd`

No solver source receives a write lease. Any checkout baseline mismatch or dependency change stops the affected lane and returns to Luna for a versioned contract update.

## Two productive lanes

### Proof lane — original mapped-bound admission

Target the actual original forwarding preservation §6 mapped-admission premise with a constructor-to-consumer induction over the original scope. Track original provider and witnesses, ordered dependencies and residual/scoped context through capture, restoration, propagation, qualifying intrusion and replay to the actual relation-local consumer. Treat FreshUse restoration and production extrusion separately; instantiate R70/R71 only at their reviewed conditional premises. Apply every established result to the original parent and name the first remaining premise. Do not substitute bucket equality, endpoint equality, insertion/acknowledgment counts or an unqualified alias graph for required lineage.

Read-only source owners: `candidate_scheme::{begin_candidate_fresh_bound,step_candidate_local_use}`, `candidate_extrusion::Work::Bound`, `candidate_intrusion` merge/recapture constructors, `candidate_context::{candidate_context_canonicalize_bounds,post_check_context}`, and typed drain/dispatch in `lib.rs`. Exact source map and proof artifacts go only to `notes/theory/2026-10-20-native-forwarding-admission.md` and `tasks/agent-loop/inbox/20261020-native-forwarding-admission.md`.

Falsifier: an authentic production consumer needs a specific original witness/residual lineage that no permitted constructor history can deliver to its actual compared instance. Stop on a missing source premise instead of changing the theorem. No tests, builds, probes, or compiler execution in this lane.

### Implementation lane — checked-out source-schedule correction

Only writable production path: `tools/inference-playground/src/runtime/program.rs`. Current `RuntimeProgram::from_hir` selects top-level computation roots from `Instruction` shape and omits `Instruction::Case`, even though that form is compiled and evaluated. The selected-definition fallback can mask this missing schedule entry. The exact repair is conditional: add `Case` to this existing syntactic “may be a computation initializer” class only if prospective review confirms that this is the established source-schedule rule and that executing a pure case initializer early preserves current module semantics. If either premise fails, return `NO_SAFE_CODE_SLICE` with the exact owner; do not add a module-mode API, fabricate Unit provenance, or claim complete Y2 execution in this sprint.

After freeze, run one `cargo check -p yu-playground` with the workspace's existing dependency configuration; do not run tests or sample binaries. No Web edits, parser changes, tuple support, imports, primitive intrinsics, host bridge, expected-output edits or temporary Yulang2 runs.

Independent code review checks the exact source rule, all instruction forms at the classifier, the Case consumer, selected-definition behavior, and that the one-line edit does not alter other root ordering or error behavior. A successful check proves compilation only, not scheduler completeness or sample behavior.

## Exact leases, resources and review

- Proof lane: 600 seconds, output pair above only; no solver writes or descendants unless Luna separately grants them.
- Implementation lane: Luna/high, 720 seconds, `tools/inference-playground/src/runtime/program.rs` only.
- Independent prospective contract/source review: 120 seconds before either lane starts.
- Fresh independent final proof/code review: 240 seconds total, disjoint from both authors; reviewer checks the original-scope application and the frozen exact diff/check receipt.
- Luna closeout and current-state synchronization: 120 seconds.
- Total fresh cap 2,040 seconds, Astra 0, no carryover. Full grant charged on issuance. Use actual runtime acknowledgements; unknown historical writers retain their current quarantined paths/reservations.

No branch/semantic adoption change or production permission is proposed. No root-level Yulang2 sample run is part of R165; the broad R149 goal continues after this bounded checkpoint with the remaining loader, tuple, primitive, role, host-write and publication gates explicit.

## STOP and next boundary

Stop on changed pins, a failed prospective premise, a counterexample, a compiler check failure, resource bound, output conflict or user STOP. Freeze only the exact result and preserve unrelated worktree changes. Next consultation is a decisive proof obstruction/result, an implementation boundary requiring a broader module-schedule design, authority/dependency/lease change, or sprint end.
