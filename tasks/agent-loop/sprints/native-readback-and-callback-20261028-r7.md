# NATIVE-READBACK-AND-CALLBACK/r7

Status: ADMITTED by Luna after R6 closed incomplete, final dispatcher consultation, and exact frozen-input reconciliation.
Branch: `yulang3`. Admission baseline commit: `16cab92bb`. Source snapshot: full isolated source tree from `7b3ad7074` with exactly three reviewed R6 provisional files as repair inputs from `d62a48c2b`; see pinned hashes below. This overlay is research-only and does not promote R6 evidence.

## Original parent, fixed meaning, and bounded outcome

The unchanged original parent remains `YulangClosure.SourceProblem.InferenceSoundness` in `notes/theory/lean/YulangClosure/Contracts.lean`:

```text
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

`SourceProblem.NativeCorrespondence` remains a separate obligation. Preserve the full supported source domain, the original quantifiers, one shared source witness, immutable-birth Value qualification, and the annotation-effect hygiene policy. No theorem or production gate is promoted by this packet.

The bounded outcome has two independent artifacts:

1. **Rust source artifact:** repair only the test-gated physical-bound replace/remove helpers in the R6 candidate so each of the eight value/effect row/atom lanes converts between its actual vector element type (`u32`, `ValueEndpointKey`, or `EffectEndpointKey`) and the enclosing `ExtrusionEndpoint`. Preserve the R6 invocation/handle association, FreshUse source-to-destination relation, current physical-slot reread, raw transformer content resolution, exact restoration-before-assertion ordering, and every existing falsifier. Keep this under `#[cfg(test)]`; do not change production behavior, API, diagnostics, fixture text, expected outputs, or language scope. The exact ordinary fixture test is `replay_constructor_lineage_observes_rejected_cross_route_authentication`.
2. **Lean callback artifact:** replace the R6 abstract capacity/error model with a bounded source-grounded frame for `InferenceSession::sample_f4_resources` and its `sample_f4_resources_with_term_override` / `sample_f4_resource_parts` path. Distinguish replay undo capacity from `route_journal.value_rows.capacity()`. Represent the observable write order and every relevant Result/panic prefix, including failure before publication, failure while preparing the test ledger, publication of ledger/counters/sample count, the `f5c_session_baseline` panic after publication but before `completed_sample`, the completed trace, and a later `observe_f5c_matrix` panic. Keep wrapper behavior distinct: physical-change is written before the callback; failure flag is written on returned `Err`, not on panic. Prove that each prefix preserves the R6 launch-evidence projection while retaining its exact exit/write prefix. Exact native size arithmetic and realizability remain separate unless actually derived.

The Lean deliverable is deliberately no larger than the callback seam. It does not model `clear_diagnostic_scratch`, seeding, child enqueue/receipt, final destination/Running writes, the full Idle/Some launch path, or any parent instance. Those owners stay OPEN. Do not reuse R6's claim that a single undo-capacity scalar represents the native route-journal lane or omit the post-publication panic prefix.

## R6 adjudication retained

R6 outcome: `tasks/agent-loop/history/native-launch-projection-20261028-r6-outcome.md`, CLOSED_INCOMPLETE/REJECTED. Independent reviewer found two static type errors in replace/remove helpers and a mismatch/omitted prefix in the resource model. No R6 checks or revisions occurred. This packet explicitly treats the three frozen R6 Rust files and R6 Lean file as **provisional repair inputs/failure references**, not accepted evidence. The R6 review deviation and stale hash incident remain recorded and are not waived.

R6 frozen repair-input hashes:

```text
candidate_scheme.rs     c79b136dd033a4d0e3f1664be670fda0c538866baa05a20c273d69a1927ead0d
candidate_context.rs    19726ef8a6034a1b99f629021b6b7e97ec638f3c1d683206de3c6eac8025a2ec
candidate_extrusion.rs  e532e7228487e125a73576cb76b8bf17c065862b049bd8d6f8fa185bb77c54af
R6 Lean candidate       eb4c5c99fee13689b4c7ee4b9cf7668ec39416e3259ed826c44204c78fc7ea13
R6 review receipt       4323f806ad9767f9da111dfca187b3866bb9bc54a203d6825ad85ea96007ebe3
R6 outcome              4fc13d56c2ce12d13e94f467545bc94ea00983de57c509e83e532f216f5348b5
```

## Exact source/dependency pins

### Rust lane inputs

All source inputs are in `isolated/native-readback-and-callback-r7/`. The three R6 repair inputs are also the initial bytes at the corresponding R7 output paths. The rest of the snapshot comes from the clean `7b3ad7074` archive.

```text
crates/yu-solver/src/candidate_scheme.rs     c79b136dd033a4d0e3f1664be670fda0c538866baa05a20c273d69a1927ead0d  [R6 repair input]
crates/yu-solver/src/candidate_context.rs    19726ef8a6034a1b99f629021b6b7e97ec638f3c1d683206de3c6eac8025a2ec  [R6 repair input]
crates/yu-solver/src/candidate_extrusion.rs  e532e7228487e125a73576cb76b8bf17c065862b049bd8d6f8fa185bb77c54af  [R6 repair input]
crates/yu-solver/src/candidate_scope.rs      9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a
crates/yu-solver/src/candidate_intrusion.rs  475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97
crates/yu-solver/src/candidate_effect.rs     7c8e4fe5270fd45cecece80dfbbdff81aa8f294546687938bf89212325fc146b
crates/yu-solver/src/candidate_source.rs     96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a
crates/yu-solver/src/lib.rs                  ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07
crates/yu-solver/Cargo.toml                  aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed
Cargo.toml                                   a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a
Cargo.lock                                   de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5
.cargo/config.toml                           c185a2b859850d94af015a9672c1568e1ef73b12612d820f596ef967b835f637
```

Before reading any assigned source body, Rust must independently hash all 12 entries and ACK exact values. Rust may read the admitted R6 review/outcome for precise findings, but no root dirty Rust files.

### Proof lane immutable input snapshot

The proof lane reads source bodies only from `isolated/native-readback-and-callback-r7-proof-input/` and the frozen R6 review/outcome. Exact pins:

```text
crates/yu-solver/src/lib.rs                                      ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07
crates/yu-solver/src/candidate_context.rs                        57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e
crates/yu-solver/src/candidate_scheme.rs                         35c58dca3748595e273cd53bfba07da2be3fd340ec63c56f6a18adea5e514fb1
crates/yu-solver/src/candidate_extrusion.rs                      80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61
crates/yu-solver/src/candidate_effect.rs                         7c8e4fe5270fd45cecece80dfbbdff81aa8f294546687938bf89212325fc146b
notes/theory/lean/YulangClosure/NativeLaunchProjectionR6.lean    eb4c5c99fee13689b4c7ee4b9cf7668ec39416e3259ed826c44204c78fc7ea13
notes/theory/lean/YulangClosure/NativeDrainOwnership.lean        d37edac29dcecc19dd90b91c3095e5385a0657310dcf08d805a8f20672872d18
notes/theory/lean/lean-toolchain                                ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c
notes/theory/lean/lakefile.toml                                  212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4
notes/theory/lean/lake-manifest.json                             058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3
notes/theory/lean/README.md                                      8d27e0b90fc04eb8a0a30606a857e564e5269e8e33e72fddbf1190cb6a7072e3
notes/theory/lean/YulangClosure/Contracts.lean                    2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e
notes/theory/2026-10-13-intrusion-source-preservation-proof.md   3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271
notes/design/2026-10-24-birth-level-scc-intrusion.md             ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae
notes/design/2026-10-10-annotation-effect-hygiene-integration.md a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18
```

Proof must acknowledge the full exact set before any dependent construction. Any changed, missing, or unpinned callback owner stops proof reads pending Luna amendment; never infer authority from source names alone.

## Assignments, outputs, and budgets

All times are reserved in full at admission. Combined assignment grant: **3,000 seconds**; no renewal/carryover.

- Rust implementation lane: registered `implementer`, Luna/high, **900 s**.
- Constructive proof lane: registered `lean_prover`, Sol/high, **900 s**.
- Fresh independent reviewer: `compiler_referee`, Sol/medium, **600 s**, including pre-check gate review and final retained-log review; starts only after both producers freeze.
- Luna primary: **600 s** for admission, integration, one focused Cargo attempt, one pinned Lean check, adjudication, records and Git.
- Astra: **0**. No descendant assignments.

Exact writes:

```text
Rust lane:
  isolated/native-readback-and-callback-r7/crates/yu-solver/src/candidate_scheme.rs
  isolated/native-readback-and-callback-r7/crates/yu-solver/src/candidate_context.rs
  isolated/native-readback-and-callback-r7/crates/yu-solver/src/candidate_extrusion.rs
  tasks/agent-loop/inbox/native-readback-and-callback-r7-rust.md
Proof lane:
  isolated/native-readback-and-callback-r7/notes/theory/lean/YulangClosure/NativeResourceCallbackR7.lean
  tasks/agent-loop/inbox/native-readback-and-callback-r7-proof.md
Reviewer:
  tasks/agent-loop/inbox/native-readback-and-callback-r7-review.md (primary persists returned receipt if reviewer runtime is read-only)
Primary:
  tasks/agent-loop/current.json
  tasks/agent-loop/history/native-readback-and-callback-20261028-r7-outcome.md
  isolated/native-readback-and-callback-r7/build-target/ (Cargo outputs, only if accepted)
  isolated/native-readback-and-callback-r7/notes/theory/lean/.lake/ (Lean cache, only if accepted)
```

No other edits, scratch files, Cargo target, Lake cache, formatter output or generated artifact is authorized. Workers perform no Git, checks, Cargo, Lean/Lake, build, test, formatter, descendants or path expansion. They verify their hashes before body reads, freeze exact outputs, report active time/resource metrics or UNKNOWN, and STOP. Rust and proof do not consume each other's mutable outputs.

## Review and conditional verification

Fresh source-first review separately adjudicates the Rust source artifact and proof/source correspondence. Reviewer returns either `ACCEPT_FOR_BOUNDED_CHECKS` for both artifacts or `REJECT`; no checks before acceptance. Reject if any lane conversion is ill-typed or not round-trip exact, observer reachability/authentication regresses, any required mutation is absent or not restored before assertion, test instrumentation reaches production, a proof declaration is only a proposition/definition, the capacity owner is conflated, any reachable error/panic prefix is omitted, the projection is assumed preserved, or a R6 unchecked claim is promoted.

Only after acceptance, Luna may run exactly one focused Cargo attempt, capped at 90 s, 1 CPU, 2 GiB RSS:

```text
cargo test --manifest-path isolated/native-readback-and-callback-r7/crates/yu-solver/Cargo.toml --locked --features shadow-apply-candidate replay_constructor_lineage_observes_rejected_cross_route_authentication
```

And one pinned Lean 4.35.0 direct module check, capped at 120 s, `-j1 -M1024`, one process:

```text
lake env lean -j1 -M1024 YulangClosure/NativeResourceCallbackR7.lean
```

Use one process at a time. The Lean module must print every delivered theorem type and every complete transitive axiom list. All failures, omissions, and actual tool versions/exits are retained. A failing check or incomplete audit closes R7 incomplete. The same reviewer performs a bounded final review of the exact retained logs and frozen hashes within the existing 600-second grant. Conditional checks do not prove source/native correspondence or the original parent.

## Non-goals and stop conditions

No production code, semantics, public API, expected output, fixture text, diagnostics, source domain, original quantifiers, A/B claim, effect policy, immutable-birth correction, or parent theorem is changed. No complete launch theorem is promised. No `clear_diagnostic_scratch` proof, enqueue/receipt theorem, runtime error redesign or later owner is in this packet.

Stop for any hash/input mismatch, changed or additional owner, callback write into the chosen evidence projection, missing prefix, overlapping writer, reviewer rejection, unknown live resource, source path outside pins, or grant boundary. Unknown writers retain their paths and reservations. Rejection does not permit revision under this contract.
