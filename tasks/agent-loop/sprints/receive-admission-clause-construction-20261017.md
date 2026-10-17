# Sprint receive-admission-clause-construction-20261017 — original F2 admission constructor

Status: READY for Luna validation and sequential exact leases.  
Branch: research/simple-sub-intrusion  
Baseline: f44908992 (prior sprint REVIEWED-PARTIAL closeout pushed).  
Parent Goal: 型推論と実行器が証明込みで実装できるまで続ける.  
Authority: user authorization to continue proof/implementation work, change procedure, and draft source bridge rules; original FORWARD-FIRST-CALL §1–2; current design authority and accepted selected constructor scopes. No semantic adoption or compiler-code authority.

## Fixed outcome and parent

Work at the original receive example and coordinates: receive(f : Unit -> alpha+) = let g = f(Unit) in g(Unit); c1 = f(Unit); c2 = g(Unit); a2 is c2's original Unit argument; xi=(nu,K,D); F2 at (sigma2,Delta2); B_in at F2's incoming ports.

Preserve the original FORWARD-FIRST-CALL A/B binders, domains, contexts, worlds, providers, observations, pending/raw-resumption/future alternatives and source/native correspondence. The original F2 incoming-view VIEW and whole-carrier CHECK inclusions are both OPEN. The reviewed bridge and control trace are conditional and do not supply the missing source admission constructor.

### Source/implementation-design — Luna/high, max 360 active seconds

Exact leases:

- notes/design/2026-10-17-receive-admission-clause-constructor.md
- tasks/agent-loop/inbox/20261017-receive-admission-clause-constructor.md

Produce an unapplied candidate source admission-clause constructor at original F2, grounded in actual source/descriptor owners and occurrences. It must specify:

1. The judgment and original source occurrences that create the inlet contract; retain F2, sigma2, Delta2, xi, original alpha/A1, declaration/definition/use paths and actual operand telescope.
2. Concrete admission clauses and source positions. Map real clause insertion and use through selected IF-Insert/IF-Use; name each original operator/primitive/import occurrence and actual event/provider/world coordinate controlled.
3. A complete clause-generation rule, including how independently imported and primitive clause families enter, and which source phases own each clause. No opaque “all guards” or restatement of desired F2 validity.
4. Separate (a) admission prerequisites deciding whether a whole carrier is accepted, (b) carrier observations/designated executions, and (c) invocation-output/result/future obligations. Draft source-contracts §3.7 G is an observation envelope, not admission.
5. Exact formulas for every clause family and its dependencies. Separate clauses fixed by approved meanings from newly proposed meanings. If completing the inventory changes observable admission, expose the smallest decision-ready alternative and its behavior, unselected.

The result is a candidate producer specification, not another conditional VIEW/CHECK theorem. It cannot accept WF_Dec(F2), L2, a complete F2 certificate, desired VIncl/CIncl or desired guard completeness as an opaque input. It cannot choose an actual provider, restrict to source executions, infer semantic Pure/Handler from Value/Computation/Unit/shape, equate I2=SAT or B_in=J_U, or derive an original guard from Q, membership or desired output.

### Proof — Astra, max 840 active seconds, starts only after source proposal freeze

Exact leases:

- notes/theory/2026-10-17-receive-admission-clause-view-check.md
- tasks/agent-loop/inbox/20261017-receive-admission-clause-view-check.md

Use the frozen proposal and attempt the original F2/xi incoming-view correspondence. Prove consequences of selected rules separately from candidate clauses. Attempt VIEW elimination and CHECK introduction independently, including complete target-domain coverage and joint witnesses for every concrete original guard. Trace exact operand telescopes, IF-Insert/Use incidences and dependent event positions. Apply any result at original c2 without replacing universal A1, provider, context, world or future binders.

Success is either a justified constructor application and local preservation result at original F2/xi with precise remaining premises, or a source-owned missing primitive clause/semantic choice with exact observable consequence and alternatives. A proof assuming the desired complete admission inventory is not success. No arbitrary-descriptor theorem beyond the producer's actual scope.

## Implementation path and authority boundary

The source proposal is the implementation-design contribution for this missing constructor. Read pinned candidate_source, candidate_call, candidate_scheme and shadow_apply owners only to trace current source occurrence, IF incidence, candidate storage and consumer paths. They retain some native incidences but do not supply the complete original admission interpretation. NO_SAFE_CODE_SLICE remains for this gap: no code may enforce SAT or another candidate admission before source clauses and meanings are independently reviewed and any new meaning is adopted.

After reviewed source clauses plus proof, Luna routes any genuinely changed meaning through authority before scoping a compiler change. Any later code lease must name generation, propagation and consumer/native paths; acceptance/principality and expected-output invariants; focused verification; rollback boundary; and independent review. This sprint authorizes no code edit, test, build, probe, runtime execution, expected-output/fixture change, semantic adoption or production promotion.

## Dependencies and pins

Rehash every input before the source lane, at the proof handoff, and before review. A mismatch requires a versioned contract update before reliance. Add and pin any new directly consumed admission or primitive clause source before using it.

| Input | SHA-256 | Use and limit |
|---|---|---|
| notes/theory/2026-10-16-first-call-joint-forward-preservation.md | f71cc442bcccb23f7e6f1aa6221b089abb8c24d1c4ce01fecef37995541c16b6 | Original A/B theorem and quantifiers. |
| notes/theory/2026-10-17-receive-c2-open-check.md | 8ad6272b9ef0612e7d7cf6915d5bb242ab29fe3968a38124d803758f56b82f02 | Actual c2 formation frontier and source owner; not a constructor. |
| notes/theory/2026-10-17-receive-sat-admission-comparison.md | 956b710546be0446ae6fd054a597196e467ce59202a08812d4c6ac349455a6e1 | Exact VIEW/CHECK obstruction and owner requests. |
| tasks/agent-loop/inbox/20261017-receive-sat-admission-comparison.md | e8e0052c6337b28f6c252e5761f882f30574c1e2cdefdca79408cef9523d8822 | Original falsifiers and owners. |
| notes/design/2026-10-17-receive-checked-inlet-view-check-bridge.md | 86c95b67c5dcb6fb03ed706838b6bde5da70639f53ba8594a85121821aa23ab5 | Reviewed unselected candidate bridge only. |
| tasks/agent-loop/inbox/20261017-receive-checked-inlet-view-check-bridge.md | f46ff320be6e018122c8e7dff149259bc6a4f4f1944f5920d4798b49e8c81a9d | Frozen proposal handoff. |
| notes/theory/2026-10-17-selected-value-entry-control-correspondence.md | 78d8b06b8304a6c1556c569b4b4fb7d455aa172c3f7aa1902563068f756b4981 | Reviewed bounded runtime control order; not admission evidence. |
| tasks/agent-loop/inbox/20261017-selected-value-entry-control-correspondence.md | 693ae61f61a1aef4e7c815a550a543d1171b71724f91b2dd274104efce8548ca | Exact source/handoff receipt. |
| notes/progress/2026-10-17-checked-inlet-bridge-and-entry-control-review.md | 7da54dda6abfa430329450c1c53100b9d1dedfddf6bf0bc91d092691c79136ad | Primary adjudication, including source-cap overrun. |
| notes/theory/2026-10-17-receive-inferred-function-view-formation.md | 7cb867df64f1d931b1667f33a6c323448d687c5d0d7fdcf9bac7535577f72590 | Reviewed absence/formation frontier. |
| tasks/agent-loop/inbox/20261017-receive-inferred-function-view-formation.md | a60a7ca1e5ea6b9d30adff7f1141b183bc8b9c8f6b8eda1302664721e7081e3a | Parent application and remaining owners. |
| notes/design/2026-10-05-inferred-function-call-views.md | 4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1 | Approved formation direction; exact rules remain open. |
| questions/2026-10-05-function-call-view-formation/approved-answer.md | 1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536 | User-approved direction; no detailed clause generator. |
| notes/design/2026-10-08-call-source-interface-definition.md | 20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c | Selected IF-Insert/IF-Use meanings and premises. |
| notes/theory/2026-10-08-call-source-interface-construction.md | 278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98 | Actual source graph constructors and incidence. |
| notes/design/2026-10-08-captured-closure-constructor-definition.md | 6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd | Selected Strict scope only. |
| notes/theory/2026-10-08-captured-call-closure-introduction.md | 0f8adcf70a72d1f46bd4ca95f3984554d8cf2ff6af6434b679e991e346ffd50f | Selected constructor premises. |
| notes/design/2026-10-08-contextual-function-membership-definition.md | 0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0 | Membership consumes admission; cannot form it. |
| notes/design/2026-10-08-native-signature-formation-definition.md | e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9 | Role/profile/support projections and premise limits. |
| notes/design/2026-10-05-source-contracts-and-common-allowance.md | 1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186 | Draft finite relation shapes; §3.7 G is not admission. |
| notes/design/2026-10-08-source-generalize-definition.md | 46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38 | Downstream closure; cannot form admission. |
| notes/theory/2026-10-08-source-generalize-definition-and-proof.md | e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240 | Desc/Shared/Event ownership and transport. |
| crates/yu-solver/src/candidate_source.rs | efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38 | Read-only source occurrence/formal owners. |
| crates/yu-solver/src/candidate_call.rs | cbad9cf51a05343eb7a29ab77aac520891467a8aa4edc3201ea3d91f978984a1 | Read-only Call/consumer incidence. |
| crates/yu-solver/src/candidate_scheme.rs | 52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a | Read-only retained Function graph representation. |
| crates/yu-solver/src/shadow_apply.rs | bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf | Read-only application/constraint consumer path; not production authority. |

## Review, resources and stop conditions

Fresh 1800-second envelope: source/implementation-design 360 + proof 840 + compiler-referee/spec-auditor/architect reviews 360 (120 each) + coordination120 + reserve120. Authors are sequential; proof begins only after source proposal freezes. One Astra assignment maximum, no descendants. Preserve three inherited UNKNOWN reservations and quarantined leases. No carryover from the prior sprint; its source-cap overrun remains in its closeout receipt.

Freeze one artifact and handoff per lane with exact hashes. Fresh independent compiler, spec and architect reviews occur sequentially after both lanes freeze. Luna adjudicates findings and integrates only reviewed bytes. At sprint end create a durable receipt, reconcile all leases, update compact current state and consult next_action_selector.

Stop at cap, dependency mismatch, unknown writer, a genuine source counterexample or any changed fixed meaning requiring user adoption. A passing static workflow check is not proof. No tests/builds/probes/runtime execution are authorized.
