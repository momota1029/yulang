# Frozen implementation/source evidence handoff

- Sprint / contract: `choose-sigma0-formation-and-call-consumer-contract-20261018-r12`, revision 2; contract SHA-256 `3979435e2e0cadf26d0aaace57c1ba7924021d2d73eb256acaf0e1c2ca015f5d`.
- Assignment / handoff revision: `ORDINARY-CALL-SOURCE-CONSUMER-CONTRACT`, revision 1.
- Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`; unchanged original quantifiers, fixed `c`; **OPEN / closure 0**.
- Baseline: `2a3f2a47d5013761f0e0717b0c6073c54c62d36`.
- Role / worker / session: implementation lane, worker ID and launch receipt unavailable in this tool context; actual worker identity `UNKNOWN`.
- Requested model / effort: Luna / high. Observed model / effort: `UNKNOWN` / `UNKNOWN`; no runtime model metadata was exposed.
- Exact leased paths, sole author: `notes/design/2026-10-18-ordinary-call-source-consumer-contract.md`; this file. No descendants.
- Outcome class: `source-native-evidence` (negative source/consumer boundary); `NO_SAFE_CODE_SLICE`.
- Artifact SHA-256: `7f1ad35c5979cea83c2f8f044b917c02405b4b06ea01f6e33dbb32e14cc42398`.
- Direct dependency/source hashes (SHA-256):

  | Path | SHA-256 |
  | --- | --- |
  | `tasks/agent-loop/sprints/choose-sigma0-formation-and-call-consumer-contract-20261018-r12.md` | `3979435e2e0cadf26d0aaace57c1ba7924021d2d73eb256acaf0e1c2ca015f5d` |
  | `crates/yu-hir/src/module.rs` | `60e91c9a51394b04af42b3ec7c284062b34fcd9faa4ea79c35b4ae58aaf460ed` |
  | `crates/yu-hir/src/shadow.rs` | `460c813cb0d2e21565df011b1d816abbc2b180cef13797a1b7b453e9ee413f66` |
  | `crates/yu-solver/src/lib.rs` | `ddd1395877d4a76e27a1dcf32af90c6fcb0e58c739610a0115c03955628350e1` |
  | `crates/yu-solver/src/candidate_source.rs` | `1a65c7afb02a4afd538a34c34086108959579e06aafe8fbcab8ad6a6b3a65f3e` |
  | `crates/yu-solver/src/candidate_call.rs` | `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479` |
  | `crates/yu-solver/src/shadow_apply.rs` | `eb0b9dcd8529e067ec8778c7888f3595ad8df466e1be4243b1d2104c853952d7` |
  | `crates/yu-core/src/shadow_call_formation.rs` | `394c763e5b4e2de6ae692ffacf22c07db8958f00129a47f1332f238c9a8eb5eb` |
  | `notes/design/2026-10-07-complete-call-contribution-definition.md` | `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e` |
  | `notes/design/2026-10-07-original-call-formation-definition.md` | `4940e031b83d3d0315f17beb51ba2e952ec64ae7d57d9ae0d086024c7305ca9f` |
  | `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
  | `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
  | `tasks/agent-loop/sprints/ordinary-hir-applied-conformance-repair-20261017.md` | `63c815697a95f0f3d851d23e1176dd7d5d48774824cb19dcfeab60d21378406a` |
  | `tasks/agent-loop/inbox/20261017-ordinary-hir-call-projection-preservation.md` | `28cc30876831203661ea237c20925249ac48ed5a9cc7fa648c36491dcb51d062` |
  | `notes/theory/2026-10-09-unary-name-application-boundary-candidate.md` | `4fd09cfc90f83e50cdf49ec27cc68dfd634ec66a0400e90778bfaf99de767949` |
  | `crates/yu-core/tests/shadow_call_formation.rs` | `1897d6bbd4e9b7e6ef6b839abdfc1943bd515c2c7cab8cb71277e8aa2925b0e2` |
  | `crates/yu-solver/src/tests/deferred_call_constraints.rs` | `ff3a879f375763f6310b0a7d1e7509ae9e66386d42fd39cc18beb5adddca6327` |

- Parent application / first missing premise: the existing source formation cases cover actual emitted `Gen-Call-0` records, while ordinary HIR Apply has no adopted source rule deriving the complete Call judgment for its general domain. Standard `ConstraintBatch::collect` classifies Apply/Group bodies as Error and retains Apply with `ApplicationTypingRuleUnresolved`. Candidate generation/admission can construct and propagate a negative Function demand, but its candidate NativeInterface has no semantic Call consumer. No complete producer-to-`ExecuteCallable`/result/future map is present. All original callee, whole carrier, provider/entry/role, context, license, complete alternatives, result and future premises remain required.
- Provisional candidate bridge (not adopted): an evidence-only `Ordinary-Apply-Call-Bridge` may connect an authentic source Apply identity to an already derived original `Q_e`, `SpecCall_e`, independent `C0_e`, same-tuple source `IF_e`, and independently justified admission/provider/carrier/license/output/future map. No premise is established here; the bridge cannot infer callability or use an endpoint-only shortcut. Potential reversible route is a default-off occurrence-keyed record populated only after actual typed Apply derivation, with standard Error/pending behavior unchanged until independently reviewed and authorized. Falsifier and cleanup path are specified in the artifact.
- Authority received in r12 rev2: recommend default adoption of a reversible interpretation only if independent review confirms it preserves observable behavior, original premises/domain and parent quantifiers; seek fresh independent review before integration. This does not adopt the missing Call rule or grant production code authority.
- Source constructors -> generated constraints -> propagation -> consumer: `ResolvedExpr::Apply`/`Group` and shadow `Form` preserve occurrence/operand identities; candidate source retains `CandidateRelation::{Apply,Group}`; `admit_candidate_fact` derives a candidate negative Function demand and admits provenance-tagged bounds into `ConstraintStore`/live propagation; no standard ordinary-Call semantic consumer reaches the original `ExecuteCallable`, `CallMem`/`C0` contract. Exact owner map and first missing rule are in the frozen artifact.
- Checks: static reads of the r12 contract, governing Call/inference definitions, direct current owners, relevant prior implementation/handoffs and source tests; source lines inspected include `lib.rs:1109-1115`, `lib.rs:1520-1538`, and `candidate_call.rs:241-278,387-425`, plus generation/admission/propagation owners. Hashes above were computed from the read inputs. No tests/builds/compiler execution/Git action; no semantic or expectation changes.
- Coverage/omissions: ordinary Apply/Group collection, candidate constraint generation, propagation and lack of the complete semantic consumer. No new source parser run, proof, runtime behavior, theorem closure, general source-domain claim beyond inspected owners, or implementation correctness claim.
- Budget: 480-second assignment bound; actual start/runtime metadata unavailable. Within available single-session work, source audit, evidence reading and two leased artifacts completed; precise active-work seconds `UNKNOWN`. No build/heavy process or test process. No budget renewal requested.
- Next related step inside r12: submit this frozen handoff and stop writes; fresh independent implementation/spec review is Luna-owned. The next source-rule/consumer evidence must come from the owning source/complete-Call rule and actual consumer authorities. No code step is ready under this packet.
- Mutual TODO: `ORDINARY-CALL-RULE-CONSUMER-1` (request only): source-rule owner supplies exact adopted ordinary Apply/Group premise and conclusion, source-domain predicate, and authentic HIR producer map; complete-Call/native owner supplies the same-tuple consumer map through whole carrier, actual returned provider/entry/role, every original alternative, complete result and future use to `ExecuteCallable`. Falsifier: no already adopted rule and current code path produce that exact map, or any tuple/premise is lost. Required input: full original rule text and source/consumer owners. No writer lease is implied.
- Worker state / write stop: `STOPPED` for writing on this freeze; no descendant leases. No scratch or generated outputs. No independent self-review; review/integration pending Luna.
