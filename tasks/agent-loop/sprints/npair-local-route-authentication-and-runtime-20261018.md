# Sprint `npair-local-route-authentication-and-runtime-20261018`

Status: ACTIVE, revision 3. Branch `research/simple-sub-intrusion`.
Baseline: `066cd49ec29a9718a884d44a325fe5580a382a66`. This is a fresh budget; no
time rolls over from `npair-original-formation-and-exact-local-route-20261018`.
Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN; original
conditions closed **0**. Preserve original theorem quantifiers, domain, C1/C2,
F1/FK1, Call, N-Transport, soundness, principality and termination. Astra0.

## Fixed outcome

Repair the Local callee route end to end from source occurrence analysis through
call authentication to the actual `shadow_apply` final-auth call-site. An
argument's later LocalUse must not replace the callee route. Ascription and
annotated Local callees remain refused unless the complete same-owner annotation
origin is authenticated at every stage. Keep all new caps scoped-only. Prove the
route invariant and its publication/rollback/accounting boundary, add positive
and negative regressions, then run the exact receive/choose fixture only after
independent CLEAN review. Keep the original theorem blockers and closure0.

The prior candidate is a research input, not approved code: exact binary diff
`notes/progress/2026-10-18-local-route-authentication-unapproved.patch`
(SHA-256 `a2e3f699ba53b79851fb34236cd96d8907cab516aa69b2c9c1abaa113350c2e1`).
The candidate source tree was restored to this sprint's baseline. Selectively
reuse the indexed-route/scoped-cap pieces only after rederiving and reviewing
them under this contract. Prior MAJOR and closeout:
`notes/progress/2026-10-18-local-route-authentication-blocked.md`
(SHA-256 `de4d3256346a8e8e6c7d4abd7d7ccb9ba8a1bdd6487dbdac41144696b6df8737`).

## Lanes and exact leases

1. **Constructive source/native proof — Sol/prover/high, 300s.** Write only:
   - `notes/theory/2026-10-18-local-route-final-authentication.md`
   - `tasks/agent-loop/inbox/20261018-local-route-final-authentication.md`

   Connect the source callee occurrence and binding identity to the retained route,
   the candidate-call authentication helper, and its actual final call-site in
   `shadow_apply`. Prove exact occurrence/slot/local identity/fresh-use equality,
   same-owner matching and scoped annotation/ascription refusal, bounded index
   association, resource accounting, and publication/rollback behavior. Include
   non-Local ascription parity and unsupported recursive/alias/Catch/If cases.
   This proves only the Local route invariant, not the original NPAIR theorem or
   semantic contribution attribution. Audit the rejected candidate rather than
   repeating its conditional claims.

2. **Implementation, regression and runtime — Luna/implementer/high, 1320s.**
   Exact leases:
   - `crates/yu-solver/src/candidate_source.rs`
   - `crates/yu-solver/src/candidate_call.rs`
   - `crates/yu-solver/src/candidate_scheme.rs`
   - `crates/yu-solver/src/shadow_apply.rs`
   - `crates/yu-solver/src/lib.rs`
   - `crates/yu-solver/src/tests/candidate_graph_call.rs`
   - `crates/yu-solver/examples/research_source_registration.rs`
   - `notes/progress/2026-10-18-local-route-runtime-validation.md`
   - `tasks/agent-loop/inbox/20261018-local-route-runtime-validation.md`

   Implement one coherent authenticated route association across the source,
   candidate_call helper and actual shadow_apply final-auth call-site. Reject a
   local callee peeled through Ascription and any annotated local binding unless
   its same-owner origin is completely checked on all three paths. Do not broaden
   refusal to existing non-Local ascriptions. Bind occurrence, local slot/id and
   use instance; later argument routes cannot change callee authentication.
   Preserve bounded/fallible allocation, lookup/work accounting and undo; cap new
   `SCOPED_RECORD_LIMIT` behavior only in scoped experiment. Keep recursive Link,
   CatchBinder, joins, unresolved aliases and other unsupported routes refused.
   Add regressions for later local argument, unscoped cap noninterference and
   annotated/ascribed local callee refusal. Do not edit fixture/expected output or
   public API.

   Resource split inside1320s: 780s implementation/freeze/review wait, 360s
   protected verification reserve, 180s evidence/handoff. After exact code freezes
   and fresh CLEAN compiler review, remeasure at least120s before each of at most
   two commands, each <=120s: (i) focused later-argument, unscoped-cap and
   annotation-refusal regressions; (ii) the existing unchanged receive/choose
   fixture with `YU_CALL_REPLAY_OBSERVER=1`. Report exact command/output/exit and
   whether a demand-bearing Replay row occurs before obstruction. No command before
   CLEAN review. If either run fails or capacity drops below120s, stop and report.

3. **Independent compiler review — fresh Sol/compiler_referee/high, 240s total.**
   Review the exact source/test/proof/handoff snapshot. Check the actual final-auth
   call-site, same-owner annotation condition, Local scheduling and later argument,
   association accounting/undo, scoped-only caps, regressions, public surface and
   runtime claims. Findings that require code edits consume this same240s cap;
   freeze revisions and issue a focused delta review. No runtime commands.

4. **Luna primary120s; contingency120s; total2100s.** Allocation: implementation
   1320 + proof300 + compiler review240 + primary120 + contingency120. Astra0,
   descendants0, no rollover. Reconcile only actual current-session receipts.

## Revision 2 — bounded final-observer repair after compile failure

This delta preserves the fixed outcome, theorem statement, source domain and
existing proof. It is authorized by the primary after the dispatcher’s
material-blocker recommendation. The failed command and its output remain part
of the record; this revision does not relabel it as a pass.

Rev1 frozen code/test snapshot, used as immutable inputs except for the exact
repair path below:

| Path | Frozen SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `1a65c7afb02a4afd538a34c34086108959579e06aafe8fbcab8ad6a6b3a65f3e` |
| `crates/yu-solver/src/candidate_call.rs` | `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479` |
| `crates/yu-solver/src/candidate_scheme.rs` | `ea48b5ec33ba9724bb761e3e04aa05cbf3eea22641830c442c8ecdcde54243d6` |
| `crates/yu-solver/src/shadow_apply.rs` | `76f2ea39151d06ba5c58aaa672488d733046e941a2c344c4e81604003d4a34ac` |
| `crates/yu-solver/src/lib.rs` | `ddd1395877d4a76e27a1dcf32af90c6fcb0e58c739610a0115c03955628350e1` |
| `crates/yu-solver/src/tests/candidate_graph_call.rs` | `e3b5c426f1f2891bddcf5c81e5845fa8d5145a242ab1d2f5dd29807b03925c16` |
| `crates/yu-solver/examples/research_source_registration.rs` | `d76cbae29f5f095ffdb5068a49556149fe4a0fcc0f5d0702ff17ad71aed35f28` |
| `notes/theory/2026-10-18-local-route-final-authentication.md` | `0fe4956c6af8ca5f909dd910fa5e38812b0d6120abcb38daaf14a9e1c4d64c4e` |
| `tasks/agent-loop/inbox/20261018-local-route-final-authentication.md` | `6da7c4ea0f26d3e0d774ca339a1ba23658f66d9c1a34ead3c2877a2bcc830aff` |

The first authorized regression command was
`timeout 120s cargo test --offline --manifest-path crates/yu-solver/Cargo.toml --features shadow-apply-candidate --lib candidate_graph_call -- --test-threads=1`.
It exited 101 before tests ran: `shadow_apply.rs:417` read nonexistent
`FrozenInferenceData.candidate_source` (E0609). This is a Rust plumbing error,
not a semantic counterexample. Dispatcher source inspection identifies the
retained mode at `candidate_graph.intrusion.effect_algebra.context.scoped_enabled`,
initialized from source mode in `start_candidate_graph`.

Reopen only these exact paths:

- `crates/yu-solver/src/shadow_apply.rs`: replace the invalid frozen-source
  access at `CandidateInference::source_call` with the retained graph mode.
  Keep the already-reviewed `observe_scoped` authentication and independent
  `admit_candidate_fact` guard unchanged. No new field or inventory heuristic.
- `notes/progress/2026-10-18-local-route-runtime-validation.md`
- `tasks/agent-loop/inbox/20261018-local-route-runtime-validation.md`

All other Rust paths, example and fixture are frozen inputs. The author may use
at most60 seconds for the exact code repair, freeze and review wait. Independent
compiler review has105 seconds left; the focused delta review is capped at90s.
The failed command is retained. After exact new hashes receive CLEAN review,
rev2 permits at most two additional commands, each bounded by120 seconds and
remeasured before start: first retry the failed focused regression command;
only if it passes, second run the unchanged receive/choose fixture with
`YU_CALL_REPLAY_OBSERVER=1`. Any new compile/test failure or capacity below120s
stops the sprint; no further retry is authorized in this revision.

Resource correction preserves total2100s without rollover: implementation
1320→1395, contingency120→45, proof300, review240, primary120. Previously
consumed implementation is883s (including15s conservative charge for the
failed command), so remaining implementation512s = repair/freeze/review60 +
verification360 + evidence/handoff92. Review135/240 is charged; at most90s of
its105s remaining may be used. Astra0, no new workers/descendants. Parent stays
OPEN and original conditions closed remain0.

## Frozen baseline and direct pins

Rehash all rows before reliance. The previous candidate's unapproved hashes are
recorded separately in the closeout note; current source starts at the restored
baseline below.

| Path | SHA-256 |
| --- | --- |
| `tasks/agent-loop/sprints/npair-original-formation-and-exact-local-route-20261018.md` | `7dc810d4967745786b1071d58b3e23917dbd4bfdf0a5d0c61833d8bf27c0017a` |
| `notes/progress/2026-10-18-local-route-authentication-blocked.md` | `de4d3256346a8e8e6c7d4abd7d7ccb9ba8a1bdd6487dbdac41144696b6df8737` |
| `notes/progress/2026-10-18-local-route-authentication-unapproved.patch` | `a2e3f699ba53b79851fb34236cd96d8907cab516aa69b2c9c1abaa113350c2e1` |
| `notes/theory/2026-10-18-operation-original-formation-compatibility.md` | `30e6c9604f5d848ca4998295eced4acb158844944ca77982f2e82ff9b8341672` |
| `notes/design/2026-10-18-operation-contribution-adoption-decision.md` | `da4309a9e00ed136ac80ade55d7140dcd201ecd3ea8ea98bcad9649649cfa783` |
| `notes/theory/2026-10-18-operation-original-formation-falsification.md` | `426e1e5ec2971655a6b0c2cde807cb3765c79a15b694f1780a17ce97d8228f62` |
| `crates/yu-solver/src/candidate_source.rs` | `09a29794eafd2c93aac69b3335120878308a6804ebd6e95c2272556b744e943b` |
| `crates/yu-solver/src/candidate_call.rs` | `2bcbab3d27e259fc4b22824980bd625014d4a19f4fa257cd74c69683c1be0359` |
| `crates/yu-solver/src/candidate_scheme.rs` | `abe1eb6d6176c035d237c3f51f7ccfe99dea5224df20de285465c510c6c2a494` |
| `crates/yu-solver/src/shadow_apply.rs` | `d29d5f6488b5824eef5dc7902b70351b5bfae1ae3d7d014ec3629267443dbc83` |
| `crates/yu-solver/src/lib.rs` | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` |
| `crates/yu-solver/src/tests/candidate_graph_call.rs` | `d7fe99792c9ade837a9ca1a206d2d24aa6cde2fa0c25979dd9f87610615e953b` |
| `crates/yu-solver/examples/research_source_registration.rs` | `d76cbae29f5f095ffdb5068a49556149fe4a0fcc0f5d0702ff17ad71aed35f28` |
| `tasks/agent-loop/fixtures/20261017-receive-choose.yu` | `969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0` |
| `notes/theory/2026-10-18-operation-original-formation-compatibility.md` | `30e6c9604f5d848ca4998295eced4acb158844944ca77982f2e82ff9b8341672` |
| `notes/design/2026-10-18-operation-contribution-adoption-decision.md` | `da4309a9e00ed136ac80ade55d7140dcd201ecd3ea8ea98bcad9649649cfa783` |
| `notes/theory/2026-10-18-operation-original-formation-falsification.md` | `426e1e5ec2971655a6b0c2cde807cb3765c79a15b694f1780a17ce97d8228f62` |

Original source/native theorem artifacts are evidence only within their reviewed
premises. Neither sprint's candidate code or a Local route proof closes original
NPAIR. The operation fixed-c, R/W/Z/domain and active-consumer blockers remain
OPEN and are carried forward without expansion into this sprint.

## End condition

End with exact frozen source hashes, fresh compiler review receipt, results from
commands actually executed, implementation/runtime evidence limits, and original
conditions closed count. Do not report a green compile or demand-bearing Replay
without the corresponding command receipt.

## Revision 3 — focused test harness source mode

Rev2's focused command compiled but two new LocalSource tests failed to find
their expected binding/source records, while the new unscoped-cap test failed
its call-count assertion. Two pre-existing tests in the same filtered run
passed. Preserve this exact exit101 and all failure output; do not count any of
the new tests as passed.

Dispatcher inspection attributes the shared test setup mismatch to
`candidate_call_hir()`, which lowers with
`lower_module_with_shadow_applications` and does not enable LocalSource. The
existing `lower_module_with_local_source` route is the authorized construction
for the three new discriminators. This is a test-harness repair only; it cannot
establish that the production Local route succeeds.

Reopen only:

- `crates/yu-solver/src/tests/candidate_graph_call.rs`
- `notes/progress/2026-10-18-local-route-runtime-validation.md`
- `tasks/agent-loop/inbox/20261018-local-route-runtime-validation.md`

Add a LocalSource-enabled helper for the three new tests and leave the existing
`candidate_call_hir()` and two pre-existing tests unchanged. Confirm parse
recovery, expected bindings/Ascription nodes, and actual Apply record presence
by source inspection. Do not weaken the scoped route, annotation/ascription
refusal, non-Local observer, or `SCOPED_RECORD_LIMIT` assertions. Do not edit
production source, example, fixture, proof, expected output or public API. If a
production defect is found, stop and dispatch it separately.

After the exact test/evidence snapshot receives CLEAN independent review, rev3
authorizes at most two additional commands, each <=120s with capacity
remeasured >=120s immediately beforehand: (1) run the same focused regression
command once; (2) only if it passes, run the unchanged receive/choose fixture
with `YU_CALL_REPLAY_OBSERVER=1`. Preserve both prior exit101 receipts. Any
failure, scope expansion or capacity shortage stops this revision; no retry.

Resource reallocation remains within2100s and does not roll over: implementation
cap1395→1530 by moving confirmed unused contingency45s and primary90s.
Implementation consumed973/1530, remaining557 = test repair/freeze/review105 +
protected verification360 + evidence/handoff92. Review consumed155/240, with
at most60s used for this delta; primary remaining30, contingency0. Proof300
consumed; Astra0; no new workers/descendants. Parent and original conditions
remain OPEN/0.
