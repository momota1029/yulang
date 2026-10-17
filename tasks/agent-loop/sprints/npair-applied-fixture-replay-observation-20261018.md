# Sprint `npair-applied-fixture-replay-observation-20261018`

Status: CLOSED-REVIEWED-PARTIAL. Branch
`research/simple-sub-intrusion`. Parent `CHOOSE-SOURCE-2 /
RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN; original conditions closed0.
Baseline: `aa808f96543474d85fe70fba92161f94cf4cfd9a`.
Preserve all original quantifiers, source domain, native correspondence, F1/FK1,
Call, N-Transport, soundness, principality and termination. Astra0.

## Fixed outcome

The unchanged receive/choose fixture has a valid `f0` and `receive`, but the
existing research harness requires a module binding `received` and stops before
candidate inference because that binding is absent. Build a companion fixture
that adds the explicit application `my received = receive f0`, and adjust the
research harness to use that companion's exact path and ModuleIdentity. Prove
the new source/HIR/Apply identity correspondence, run the reviewed harness once,
and determine whether its exact `received` Apply reaches a demand-bearing Replay
observation or the next exact obstruction. Keep the original fixture unchanged.

This is a source-to-native reachability result only. A passing harness or Replay
row does not identify original mathematical `c`, prove universal R/W/Z/domain
actions, active-consumer reflection, NPAIR, F1/FK1, Call, soundness,
principality, termination, or production readiness. Original closure stays0.

## Lanes and exact leases

1. **Source/native construction — Sol/prover/high, 120s.** Write only:
   - `notes/theory/2026-10-18-receive-applied-source-correspondence.md`
   - `tasks/agent-loop/inbox/20261018-receive-applied-source-correspondence.md`

   Compare original and companion fixture. Require exact parsed-node/source key,
   new ModuleIdentity, declaration/use ownership, LocalSource Apply occurrence,
   binding `received`, `f0`, `receive`, and call observer ownership. Do not reuse
   old artifact keys across the new module identity or equate source identity
   with original semantic `c`. State exactly which edges are statically proved
   and which need the run.

2. **Companion fixture/harness/runtime — Luna/implementer/high, 540s.** Write
   only:
   - `tasks/agent-loop/fixtures/20261018-receive-choose-applied.yu`
   - `crates/yu-solver/examples/research_source_registration.rs`
   - `notes/progress/2026-10-18-receive-applied-replay-observation.md`
   - `tasks/agent-loop/inbox/20261018-receive-applied-replay-observation.md`

   The companion may differ from the original fixture only by the trailing
   explicit application declaration. Change the harness include, disk path,
   expected ModuleIdentity and comments to the companion; preserve source
   ownership checks and require exactly one `received` Apply to match all
   occurrence/owner/operand/source-key/scope evidence. Do not weaken diagnostics,
   bypass failed admission, parse stderr as a proof, or change public APIs.

   Resource split: 240s edit/freeze/review wait, protected 240s verification,
   60s evidence/handoff. After exact-byte CLEAN review, remeasure >=120s and run
   at most one command, <=120s:
   `YU_CALL_REPLAY_OBSERVER=1 timeout 120s cargo run --offline --manifest-path crates/yu-solver/Cargo.toml --example research_source_registration --features shadow-apply-candidate`
   Preserve complete command/stdout/stderr/exit and whether a demand-bearing
   Replay row occurs before obstruction. On failure, stop; no retry in this
   sprint. Do not rerun the already-passing focused five-test command.

3. **Fresh independent compiler review — Sol/compiler_referee/high, 120s.**
   Review exact changed fixture/harness/proof/runtime snapshot and all direct
   pins. Check fixture delta, ModuleIdentity and source-key ownership, exact
   Apply correspondence, diagnostic boundaries and observer claim. No commands
   or edits. Any requested change consumes the same review cap; obtain a focused
   delta review before execution.

4. **Luna primary60s; reserve60s; total900s.** Allocation: source/native120 +
   implementation540 + review120 + primary60 + reserve60. No rollover from the
   prior sprint. Astra0; no new descendants; children never start teams.

## Frozen inputs and direct pins

Rehash before reliance. Previous sprint closeout is commit
`aa808f96543474d85fe70fba92161f94cf4cfd9a`; old review and failure/runtime
receipts are evidence only.

| Path | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `1a65c7afb02a4afd538a34c34086108959579e06aafe8fbcab8ad6a6b3a65f3e` |
| `crates/yu-solver/src/candidate_call.rs` | `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479` |
| `crates/yu-solver/src/candidate_scheme.rs` | `ea48b5ec33ba9724bb761e3e04aa05cbf3eea22641830c442c8ecdcde54243d6` |
| `crates/yu-solver/src/shadow_apply.rs` | `51d1d1534d86181dce6caf0638f5c55e7c3bad6d764c3da5c4c9af10421335ac` |
| `crates/yu-solver/src/lib.rs` | `ddd1395877d4a76e27a1dcf32af90c6fcb0e58c739610a0115c03955628350e1` |
| `crates/yu-solver/src/tests/candidate_graph_call.rs` | `21c555b57a8684c9f8971e9180ac0ee732dc7a82834db606241653869987f55b` |
| `crates/yu-solver/examples/research_source_registration.rs` | `d76cbae29f5f095ffdb5068a49556149fe4a0fcc0f5d0702ff17ad71aed35f28` |
| `tasks/agent-loop/fixtures/20261017-receive-choose.yu` | `969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0` |
| `notes/theory/2026-10-18-local-route-final-authentication.md` | `0fe4956c6af8ca5f909dd910fa5e38812b0d6120abcb38daaf14a9e1c4d64c4e` |
| `tasks/agent-loop/inbox/20261018-local-route-final-authentication.md` | `6da7c4ea0f26d3e0d774ca339a1ba23658f66d9c1a34ead3c2877a2bcc830aff` |
| `notes/progress/2026-10-18-local-route-runtime-validation.md` | `3ecb9bceae6f3c75cddb973520d93683bfb1a3ed50d37238131086751dec3a9b` |
| `tasks/agent-loop/inbox/20261018-local-route-runtime-validation.md` | `5bcdc76544c0d025660a77f024c31ad86698e6381fbcf7494fb973b066a0d9b5` |

## End condition

Freeze exact hashes and fresh review/runtime receipts. Report whether the
companion reaches a demand-bearing Replay and the exact stopping point. Report
original theorem conditions closed (expected0); do not promote reachability to
semantic attribution or theorem closure.

## Primary closeout rev2

The companion fixture and harness were independently reviewed CLEAN at the
frozen rev1 hashes and committed with the source/native proof as `ad4af2393`.
The proof establishes conditional source/HIR/Apply correspondence through the
exact `ModuleDef(receive)` and `ModuleDef(f0)` operands and final observer
target. It does not establish the original semantic `c` or close a parent
condition.

After CLEAN review and capacity remeasurement, the exact authorized observer
command ran once and exited `0`. Available captured output confirms the
383-byte companion, zero parser structural recoveries, the expected
ModuleIdentity, the exact `received` operands, candidate inference start and
`candidate.source_call[3]` source correspondence. The tool truncated stdout
inside the relation/Replay rows; the complete transcript is unavailable.
Therefore demand-bearing Replay status is **UNKNOWN**, not present or absent.
The run was not retried. Detailed primary runtime evidence is in
`notes/progress/2026-10-18-receive-applied-replay-observation.md` and its inbox
receipt. The CLEAN review applies to the committed rev1 snapshot; the later
runtime addendum records only the execution facts and capture limitation.

Original conditions resolved: **0**. Parent remains OPEN. No semantic rule,
quantifier, source domain, test expectation or production gate changed. Only the
previously passing five focused tests remain test evidence; the new companion
harness completed once with exit0.

Conservative sprint accounting: **660/900 seconds charged** (proof120,
implementation edit/freeze cap240 because elapsed was unavailable, review120,
single runtime command120, primary60). **240 seconds retired**; no rollover.
The runtime command allocation is consumed, and a second invocation is outside
this sprint.

Next useful sprint: keep the reviewed companion and harness bytes fixed, capture
the one authorized run to a durable bounded log so output cannot be truncated,
then independently join any Replay row to the authenticated
`candidate.source_call[index]`, matching native root and ordered endpoints. If
no row survives the full capture, record the exact obstruction. This follow-up
must use a fresh sprint budget and must not treat the current `UNKNOWN` as
evidence of absence.
