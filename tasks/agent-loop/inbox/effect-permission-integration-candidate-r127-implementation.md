# R127 implementation handoff — in-memory composition only

Sprint `EFFECT-PERMISSION-INTEGRATION-CANDIDATE/20261102-R127`, contract rev 1, SHA-256 `aa6cb58fb8c728ff021a87b9e86ea9ce2251142bee283928816e97848317996a`; manifest `tasks/agent-loop/sprints/effect-permission-integration-candidate-20261102-r127-inputs-r1.json`, SHA-256 `04566bb0f82e2d34bf4f6e843aa0534c193d37f1a87326066c298e2cabec9cce`; admission `tasks/agent-loop/history/effect-permission-integration-candidate-20261102-r127-admission.md`.

Assignment `R127-IMPLEMENTATION-1`; worker `/root/r127_integration_candidate`; sole output lease is this file. Requested model/effort `gpt-6-luna/high`; observed model, effort and separate launch receipt are UNKNOWN. This is a source-qualified in-memory candidate composition, not source integration, compilation, test evidence, proof closure or production approval.

## Baselines and frozen direct inputs

Current baseline `yulang3` is commit `b5f4df2509ad9c8dba311a6139354bc3f7d33404`; R111 source baseline is `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`. For each of the three files, read-only `git show` SHA-256 and byte length matched at both commits:

| File | Baseline SHA-256 | Bytes |
| --- | --- | ---: |
| `crates/yu-solver/src/lib.rs` | `c43fcc4f39e4ba8bfea10aa39879c37973100d9f4b8bdef71fa5b3dc3fae01df` | 1,660,759 |
| `crates/yu-solver/src/candidate_receiver.rs` | `6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2` | 292,001 |
| `crates/yu-solver/src/candidate_effect.rs` | `1c80c55c62b724b9d2080bd2ddcdabfa35a5ba641c1bf45d9735dfd7fd05be41` | 301,836 |

Reused exact R111 four-repair target hashes from rev3 handoff `54a79a1b4f49d75b78bd3c3e96ff2c317941c57e24dfbad6e2c441309f131d9d`: `lib.rs` `6eb6b5df29bda1d1bd1fecabcbc2cc6e85e777dda2045f1d1ab86084f64cd84f`; `candidate_receiver.rs` `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf`; `candidate_effect.rs` `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01`. The receiver's four replacement reconstruction independently reproduced the pinned R111 SHA exactly (291,827 bytes).

R117 revision-2 patch SHA-256 `c3858b35433433806e7f8a01f27c12ab5491a8116e6e88c2b1e32a6ccf5beab1`; its independently accepted patch review is `tasks/agent-loop/inbox/effect-permission-native-decoder-r117-review2.md`, SHA-256 `a47cfe5a54cc2d22b3fcd2834bed3f3c959ba85cfcb28cf38ed095db06488664`. R119 corrected patch SHA-256 `5bc02af31d3c80ecae3848760b8723195dd568a7bf924cfc8b3b614b1227a18a`; R119 Rust handoff SHA-256 `731cc66eacc5f271bdf1d70054b8430ac0641ac55ac07281123f9fe5645e8e98`, review SHA-256 `e4b9a3bf3d6b28ef2d1b5d77bbbc6345826f1a96d868efe10994dfac83fb230b`. R120 exact ordered full-context composition receipt SHA-256 `0c503338c144eab1feb2fce128227a7409f312b947876cd504f5b1af9fd1050e`; its independent review is recorded at `tasks/agent-loop/inbox/effect-permission-member-trace-r120-review.md`.

R119's earlier malformed patch revision was rejected by its review and was not used. Only the corrected `5bc02…` artifact, already used by R120, was used here. R120's receiver result `108a50…` is not claimed as this result: R120 began from the unmodified baseline, whereas this packet first reconstructs R111's four receiver repairs.

## Composition and exact ranges

Composition was performed only in process memory: (1) start from the authenticated `d177` receiver blob; (2) apply the four R111 receiver replacements below, checking each complete old text occurs exactly once; (3) apply R117, then R119, parsing every unified-diff hunk and matching its entire old payload in the remaining ordered input; (4) concatenate untouched input bytes and exact replacement payloads, retaining line terminators. Each R117/R119 hunk had one unique full-context match after the prior consumed region. Header counts equaled parsed old/new payload counts. No context was dropped, fuzz used, or bytes omitted; all bytes outside listed hunks are copied verbatim. `lib.rs` and `candidate_effect.rs` retain their R111 targets because R117/R119 only patch `candidate_receiver.rs`.

Ranges are 1-based and show actual input and output starts at each sequential stage; old/new counts are complete hunk payload line counts.

| Stage / hunk | Header old start | Actual input range | Actual output range | Old/new lines | Unique matches |
| --- | ---: | --- | --- | ---: | ---: |
| R111 receiver 1 | 4186 | 4186–4186 | 4186–4186 | 1/1 | 1 |
| R111 receiver 2 | 4385 | 4385–4385 | 4385–4385 | 1/1 | 1 |
| R111 receiver 3 | 4433 | 4433–4436 | 4433–4433 | 4/1 | 1 |
| R111 receiver 4 | 4628 advertised | 4625–4625 after prior R111 edit | 4625–4625 | 1/1 | 1 |
| R117/1 | 231 | 231–234 | 231–238 | 4/8 | 1 |
| R117/2 | 603 | 607–613 | 607–617 | 7/11 | 1 |
| R117/3 | 1860 | 1868–1879 | 1868–1899 | 12/32 | 1 |
| R117/4 | 4844 | 4869–4871 | 4869–4875 | 3/7 | 1 |
| R117/5 | 5052 | 5081–5084 | 5081–5090 | 4/10 | 1 |
| R117/6 | 5106 | 5144–5155 | 5144–5186 | 12/43 | 1 |
| R119/1 | 237 | 234–238 | 234–239 | 5/6 | 1 |
| R119/2 | 610 | 612–615 | 612–616 | 4/5 | 1 |
| R119/3 | 1878 | 1881–1887 | 1881–1889 | 7/9 | 1 |
| R119/4 | 4880 | 4876–4879 | 4876–4880 | 4/5 | 1 |
| R119/5 | 5145 | 5170–5182 | 5170–5188 | 13/19 | 1 |
| R119/6 | 5158 | 5190–5197 | 5190–5197 | 8/8 | 1 |

Unique-context relocation is part of the stated R120 method. In particular, this report does not claim strict zero-offset application at advertised hunk headers. The compositions succeeded without an ambiguous or missing context.

## Combined virtual candidate hashes

| File | Combined candidate SHA-256 | Bytes / lines |
| --- | --- | --- |
| `crates/yu-solver/src/lib.rs` | `6eb6b5df29bda1d1bd1fecabcbc2cc6e85e777dda2045f1d1ab86084f64cd84f` | 1,660,798 bytes |
| `crates/yu-solver/src/candidate_receiver.rs` | `335f5f2cd4841dd8288306623ee863606e355b9ceda6948ab6877d944bed3165` | 296,602 bytes / 5,872 lines |
| `crates/yu-solver/src/candidate_effect.rs` | `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01` | 301,873 bytes |

## Preserved behavior evidence and interpretation limits

R111's `owns_source_root` replacement delegates the existing Definition and Expression checks and uses the existing Member ownership rule; it does not skip registered-lambda, occurrence, parameter, or source-owner validation. Its other receiver edits dereference the owned/reference occurrence comparisons. R111's lib repairs name the existing `SolveAvailabilityError::IdentityExhausted`, and its effect edit adds the `RowKey` import.

R117's existing guarded capture/package path remains in place: owner/batch/live-state identity, provider/declaration/selected-arm operation identity, typed native view/member checks, unique registration-key lookup, separate packed storage index, and captured-record pointer checks. R119 carries `permission_member_index` as `Option<usize>` from the first `permission.concrete.iter().position(...)`, copies it alongside the same borrowed permission reference into the request, then checks `.get(index)` on `self.catch.permission.concrete` at the existing consumer. Registration, packed permission slot, native member coordinate, concrete member index, and family value remain distinct.

The source excerpt does not make the concrete-vector starting-address comparison a length or provenance proof. For `[4,9,9]`, the first search gives index 1; a tampered index 2 still reads an equal family and can pass the local indexed-family guard. Thus successful direct field transport is the source-level reason for first-match preservation; that local guard alone does not prove it. Empty/missing member, out-of-range/`None`, duplicate registration and foreign owner/state checks are guard observations, not executed reachability results. This composition does not establish Rust borrow checking or a Rust-to-Lean operational relation. `U=T`/R126 source equations are untouched; no R126 source hunk exists.

Prior evidence reused: R111 rev3's exact target reconstruction and review history; R117 revision-2 accepted static review; R119 corrected patch and R120's reviewed composition method and independent source-trace review. Rejected: R119's prior malformed patch revision and any inference that R120's no-R111 receiver hash applies to this combined target. No standalone R111 reconstruction or environment feasibility was repeated beyond applying the exact four receiver replacements to verify the pinned target while composing.

## Checks, resources, gates, and next step

Read-only `git show` confirmed the `d177`/`b5f4` source hashes above. Inline `python3` in-memory processing checked the four R111 unique replacements, R117/R119 header payload counts, ordered unique full-context matches, ranges, and final SHA-256 values. The initial `python` executable lookup failed with exit 127; `python3` was available and the checks completed. No tests, compiler/build, Lean/checker, patch application to a file, source edits, dirty/quarantined source reads, filesystem scratch/cache/copy/worktree, environment/storage probe or Git mutation occurred. Exact active wall/CPU/RSS telemetry is UNKNOWN; the assignment bound is 300 seconds, and only bounded source/patch byte strings were held in memory. No descendants or scratch paths were created.

R111's independent source/storage review and private aggregate 6-GiB compile gate remain unmet; its single compile allowance remains unused and blocked. R127 cannot authorize integration or relax that gate. The proposed receiver composition only observes the candidate capture-to-consumer path; it does not execute source-to-constraints-to-propagation-to-execution, change semantics, establish proof correspondence, or close original soundness/effect-hygiene claims. The proof lane should bind these exact virtual hashes to R126/R121/R119 evidence; after both handoffs freeze, the admitted fresh independent compiler referee can challenge the combined bytes and source trace. Primary-only integration remains gated by the existing R111 review/storage requirements and Luna's authority.

Writes STOPPED after this handoff. No additional paths or disposable scratch outputs were created.
