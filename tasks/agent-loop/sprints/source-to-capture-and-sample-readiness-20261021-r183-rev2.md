# R183 — source-to-Capture and sample readiness (revision 2)

Status: prospective-review candidate; no worker or compiler work is active.
Revision 2 supersedes the NOT-CLEAN prospective candidate without changing the
original goal or proof scope. Branch `research/simple-sub-intrusion`; baseline
commit `6c690b00b17c71ac354cdc1a714d757aae0fe8b8`, tree
`9f66e440f3ecf99c2cd8e9a4c6005a802301c5be` (R182 closeout).

## Outcome

Advance the original forwarding-preservation §6 source-to-provider premise by
tracing original Name/body constraints through the same provider's Capture,
shared-anchor, origin-transfer, extrusion and FreshUse lower-input path, while
establishing the demand upper lineage independently. Use R182's reviewed
common-row ordered-Replay/Function/check result only under its stated premises.
Return either the forward derivation for the contracted constructors or the
first precise missing constructor law and owner. Keep provider/use identity and
both ordered Replay inputs explicit; endpoint equality, OR ancestry, inventory,
diagnostics and observer summaries are not substitutes.

In parallel, prepare an activation-ready path for unchanged Web sample
compatibility. The sample lane produces a verified owner/authority/check
envelope and exact next actions for open sample routes; it does not execute,
edit compiler code or select language semantics. The full goal is not redefined
around the countdown sample.

## Parent, fixture and fixed dependencies

Parent: `notes/theory/2026-10-15-computation-forwarding-preservation.md`,
SHA-256 `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`.
Unchanged source fixture: `tools/inference-playground/examples/r171-formal-name-forwarding.yu`,
SHA-256 `cb2fff33a1ab983a932064cc1699d9f4f4a8d5e00d52986525884d42bc58234f`.

R182 contract SHA-256
`6388a401a28efb1e1f1ff025c29a6f2deb2b020c476824acde0ff258946a8efd`;
R182 proof note `ab812298ddb274864f334a484f9aa6a8a3fe301dcc1371943d1a21c317a22857`;
R182 proof handoff `73ba5b4061d58c61cae23f36645f47ea15cd60209239a983ad432bcaf2654b94`;
R182 implementation handoff `41b88416c45fbd91ccdc9f606f7efd6513cfd188811bb863f2277d6dfb04a084`.
Prospective current-state input `tasks/agent-loop/current.json` SHA-256
`40d7150d019de430c9037f08bc289e3f81a9122060416939db144f30d4442d37`.

R147's closed reviewed-proposal receipt is
`notes/progress/2026-10-20-r147-closeout.md`, SHA-256
`853541e3f883a5f235fb366b752515220f9277cbe6b789f0e59b3d4e35f4e6a5`. It
records CLEAN prospective reviews and a CLEAN final compiler/source review of
the exact five-artifact bundle below, and records that user approval is still
pending. The R147 decision file's DRAFT status means the semantic option is
not adopted; it does not mean that the proposal bundle lacks its final review.
Prospective review must verify all five bundle hashes against that receipt.

| R147 bundle artifact | SHA-256 |
|---|---|
| Contract rev2, `tasks/agent-loop/sprints/braced-if-approval-packet-20261020-r147-rev2.md` | `87ec019b57a2e885bff6aab5e7cf16929526ebb07df593646f495442184ff281` |
| Decision draft, `notes/design/2026-10-20-braced-if-compatibility-r147.md` | `2dbbf05c2c74810c4684a71d81933d4b6b4a9be2067dcc60b943bb090ff64f12` |
| Conditional source note, `notes/theory/2026-10-20-braced-if-elaboration-r147.md` | `f2a9ef20bc981ba40310aaca5ff20f2c0edaff6e60f5e07e63f13fdd33e4094b` |
| Proof handoff, `tasks/agent-loop/inbox/20261020-r147-proof.md` | `02890c687a4be4f82d071cc9c24d4ee728192107e48f0f74dc93fd1b553e1887` |
| Luna decision handoff, `tasks/agent-loop/inbox/20261020-r147-decision-packet.md` | `d3bb3264ffb64df0d7948e3460c43ce1f037a4bd51ef7ebb4fb3de8dea031355` |

Other readiness references are independently pinned:

| Artifact | SHA-256 |
|---|---|
| R167 module schedule proof, `notes/theory/2026-10-20-r167-module-schedule-proof.md` | `f24e69f293d7f56c663a6e3ebdb64b41b7eee9bf94ceda710ab942d82e8ccb8a` |
| R149 contract rev10, `tasks/agent-loop/sprints/yulang2-types-console-20261020-r149-rev10.md` | `31214917352b673c7467873b60d5db8e470e4d16c8370d882c266a7fcef5b3e9` |

## Exact source inputs for the proof lane

Use only the twenty immutable source files and four roots already pinned by
R182's contract/note. Their complete hashes and modes must be rechecked from
the immutable roots before activation and by final review. Do not read mutable
checkout copies as evidence.

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
| `candidate_call.rs` | `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479` | same |
| `candidate_source.rs` | `cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7` | same |

The first nine pairs are flattened files directly under
`/tmp/r178-inputs/{baseline-7ec64a378,candidate-e9a7a4f}/`; the `candidate_scope.rs`
pair is directly under `/tmp/r181-inputs/{baseline-a8f7c4d74,candidate-a8f7c4d74}/`.
All files must remain `0444`, roots `0555`. No additional owner is admitted;
report a missing constructor path/definition as a dependency request to Luna.

## Lanes and exact outputs

After prospective CLEAN and Luna activation, the proof lane owns only:

- `notes/theory/2026-10-21-r183-source-to-capture.md`
- `tasks/agent-loop/inbox/20261021-r183-proof-result.md`

The Luna/high sample-readiness lane owns only
`tasks/agent-loop/inbox/20261021-r183-sample-readiness-result.md` plus sequential
contract/current-state revisions. It verifies the complete R147 reviewed bundle
above and records exact next actions for R167/R149. It may not execute, edit
compiler code or choose semantics.

The concrete R147 sample is `web/playground/examples/yulang2-ordinary-islands.yu`;
eventual success evidence must include `countdown_result -> 8` through parser,
HIR, inference, evaluator, CLI/WASM/Web, without changing the fixture or
expected outputs. R147 Option A covers one non-record expression; Option B
covers ordinary expression lists and explicit record cases. B is recommended
for breadth, but no option/revision has user approval. The separate
implementation contract remains unauthorized until the user's exact decision.

Independent sample barriers remain separate, with concrete next actions:

- R167 `R167-CASE-FETCH-1`: establish the source-owned, occurrence-qualified
  fetch-class law for an admitted Case binding and carry that association through
  Group/Ascription/empty-Block forwarding into `RuntimeProgram::from_hir`'s
  schedule consumer. Do not infer the law from effects, purity or instruction
  shape. Only then reconsider the dependent public whole-module entry.
- R149 Types/Console: freeze the authentic module/declaration resolver and
  reachable library/role prerequisite closure, then establish the tuple and
  primitive public type constructors, source-order initializer schedule and
  host publication/continuation path with fresh review before a complete
  implementation contract. Do not treat this as a prerequisite to the
  independent R147 selected-definition countdown route.

No sample path is already activated by R183. No source inspection, compiler
edits, tests, builds, CLI/WASM/browser/evaluator/compiler/Yulang2 execution,
probes, network, nested CLI, scratch, or descendants are authorized. R147's
exact-option approval and separate implementation-contract gate remain in
force. Luna is the sole Git integrator.

## Review, resources and stop conditions

Fresh cap 3000s, no carryover: preparation/activation 240; prospective review
120; proof 1200; sample readiness 600; final independent reviews 360; conditional
delta review 120; closeout 360. Astra 0; execution 0. UNKNOWN legacy workers
retain their quarantined leases and reservations.

Prospective review checks every dependency/source pin, modes, authority and
disjoint output leases. Final reviewers independently reconstruct the proof's
forward Capture/anchor path and the sample readiness's reviewed R147 bundle and
R167/R149 next-action boundaries. Luna freezes outcomes and updates current
state, adjudicates, stages only exact approved paths, and owns commits/pushes.

Stop on pin drift, a required unleased owner, a counterexample, authority
ambiguity, a request for execution/code, or the exact budget boundary. A
counterexample or new owner returns to Luna for dispatch; safe independent work
continues. Next dispatcher boundary: material proof result, demonstrated
missing owner/authority, code-ready integration seam, or budget boundary.
