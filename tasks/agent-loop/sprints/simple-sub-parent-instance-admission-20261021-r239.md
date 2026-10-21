# Sprint R239 — Parent instance mapped-bound admission

Status: ACTIVE_PROOF_SOURCE_AUDIT; Luna sole primary. No child workers.
Baseline: `0a9c6a797` (`research/simple-sub-intrusion`), after R238 partial freeze.

## Fixed parent and outcome

Parent: `notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1, 6–7, SHA-256 `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`.
R238's exact raw-fiber constructor result is frozen at `notes/theory/2026-10-21-r238-backward-source-alias-schedule.md`, SHA-256 `3263838c2810c543d81b76a17e6225a40528ba2eb28b6c44d6edcff9cdc0b905`; contract SHA-256 `928e2b33167961d5f6d816292a5c0c0a349caa49482f247c115b43b0b605c5ae`.

Derive the direct-Name provider-use base case for one authentic instance map `mu`: trace the original registered inequalities `e_t<=e_n<=e_R` and `e_n<=e_t` through source emission, capture, consistent FreshUse mapping, bound restoration/replay, successful admission/activation, and the actual Function comparison. Apply any established lemma immediately to the conditional parent implication. Preserve §1's one shared satisfying assignment, original formals, unbounded finite chain length, repeated calls, simultaneous entries and every finite prefix.

Success is either (a) a source-to-native labelled forward simulation matching each required mapped inequality to its actual admission/activation and use event, or (b) the earliest exact missing constructor/admission premise with its owner and a falsifier. This base case cannot close the chain induction, R71/R72, or the parent. Finite source misses do not refute universal claims.

## Method and falsifiers

Label each original inequality by source formal and constructor. Follow labels through `candidate_source` slot-4 emission, `candidate_scheme` capture and one authentic FreshUse map, `candidate_extrusion` restoration, `candidate_context` activation/replay, and the actual Apply Function comparison. Keep Module and retained Local routes distinct; include rollback/resumption only where the selected path uses them. Relate solver RelationIds/BoundKeys to source mapped bounds only through an explicit source-to-native correspondence. Retained relation existence, endpoint equality, or a ReplayOperationId alone is not admission/activation evidence.

Falsifier: any required labelled bound lacks authentic capture, consistent mapping, successful restoration, actual admission/activation, or the per-use Apply/next-provider join. A result that relies on R71/R72's canonical-child route must first show that the parent-required mapped bound depends on that route.

## Lanes, leases, limits

Serial Luna proof/source lane; no child workers or Astra. No initial code edits, tests or builds. Implementation is `NO_SAFE_CODE_SLICE` until an approved parent-required admission is shown missing; only then propose an owner-specific repair or a separately leased minimal observer. No semantic changes or production authority.

Exact write leases:
- `tasks/agent-loop/sprints/simple-sub-parent-instance-admission-20261021-r239.md`
- `notes/theory/2026-10-21-r239-parent-instance-admission.md`
- `tasks/agent-loop/current.json`

Resource cap: 900 seconds, serial; no carryover from R238. Freeze on a decisive missing supplier, source-qualified counterexample, authority/dependency/lease change, substantive result, or budget boundary. No parent closure without fresh independent review. Validate and commit/push only coherent leased paths after checking the complete outbound range.

## Frozen direct dependencies

```text
3263838c2810c543d81b76a17e6225a40528ba2eb28b6c44d6edcff9cdc0b905  notes/theory/2026-10-21-r238-backward-source-alias-schedule.md
928e2b33167961d5f6d816292a5c0c0a349caa49482f247c115b43b0b605c5ae  tasks/agent-loop/sprints/simple-sub-backward-source-alias-20261021-r238-rev2.md
95dce8a15b7e9c57b94f6c5741cb7af1b4056fe32af66fb7adfe41db99c68144  notes/theory/2026-10-21-r236-attach-lineage-induction.md
9d93bf9e4579adf8ac88d05325431610757a1c844e85894b47308aa86a7a291e  notes/theory/2026-10-21-r237-source-occurrence-consumer-route.md
5185481127cb619d66d49025c0a20ee7d829bc1e7a46072a05adecf4d22aa891  crates/yu-solver/src/candidate_extrusion.rs
90665143f127394316b950d039fc498d460ac680df20b2387911a2fbdcaaeee1  crates/yu-solver/src/candidate_context.rs
45324aaec3825b1bf5cb15811ce309b8ff2dc020d5882383c0ed33d9d0b779f8  crates/yu-solver/src/candidate_effect.rs
135b72655d948d5035b21eaddce9fbeb0260c49bc3093e4bf2df73b03d88c4a1  crates/yu-solver/src/candidate_scheme.rs
475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97  crates/yu-solver/src/candidate_intrusion.rs
90ed01915688b9c13c95593ddce296e7e3702a623e23dd4b9255d718b380a599  crates/yu-solver/src/candidate_source.rs
50ad99c3afabb12816e9ec17fe50372bac758964699519d9ce6f1fc1f6649599  crates/yu-solver/src/shadow_apply.rs
285a39449360b050d7689f9e52f400b821e651ec9ce300bd14a1a3d9a9ab8b64  crates/yu-solver/src/lib.rs
```
