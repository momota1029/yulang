# Sprint R334 — Independent review of R333 FieldTail transport

Status: ACTIVE; direct-primary; review target frozen at `17e57af2c4605d7084c7d76792b115674776bbe2`.
Revision: 1. Parent: unchanged Yulang2 playground catalog and Simple-sub obligations.
Selector: `/root/r333_selector` recommends review first because provider-role transport is a premise for dependent inference work; no Button branch-discharge code slice is currently authorized by established source/dispatch evidence.

## Original goal and sprint outcome

Keep the user's original goal unchanged: construct and prove Yulang type inference/runtime so the same original Yulang2 playground samples work on the evaluation machine. Preserve all source bytes, outputs, ordinary semantics, source/native correspondence, and the original Simple-sub A/B quantifiers. Source/native, receiving, principality, catalog, independent-review and production gates remain OPEN unless each is separately discharged.

Review the complete R333 change from baseline `85f41587e` through frozen commit `17e57af2c4605d7084c7d76792b115674776bbe2`. Decide whether its FieldTail provider-role transport and merge/removal laws are sound for the claimed source path, identify exact counterexamples or missing premises, and let the primary adjudicate. Success is a frozen independent report plus explicit primary disposition: accepted as bounded implementation evidence, repaired under a new exact lease and delta-reviewed, or rejected with the surviving obstruction. No review result alone closes a parent theorem or production gate.

## Frozen review target and dependencies

- `crates/yu-solver/src/candidate_scheme.rs` at `17e57af2c4605d7084c7d76792b115674776bbe2`: SHA-256 `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` (complete R333 diff is 517 lines).
- `tasks/agent-loop/sprints/r333-fieldtail-descriptor-transport-20261023.md`: SHA-256 `72937dff85d174d0abb0d9d318fe19ab6a1a1eaf7010cd943666828918993028`.
- `notes/theory/2026-10-23-r333-fieldtail-descriptor-transport.md`: SHA-256 `945964c75ba27c8ef6bc008e7cc4944d910e2eecd684355b976635fee4c64127`.
- Read-only constructor/consumer context as needed: `candidate_source.rs`, `candidate_effect.rs`, `candidate_value_graph.rs`, `shadow_apply.rs`, `yu-hir` local source/source identity/shadow modules, and the source regression in `candidate_scheme.rs`.
- The reviewer must inspect the pinned commit blob, not mutable working-tree bytes, and independently trace the relevant producers and consumers. R333 author's note is a locator/claim list, not proof.

## Review questions, falsifier and limits

Assess each claim separately:
1. All pending/retained/definition-local coalescing merges the authenticated `required_roles` set before selection or removal; immutable source/member/candidate metadata collisions fail closed.
2. Definition, Member and Expression provider lookup is tied to the exact source owner, occurrence, origin, immutable metadata and ordered source guards; it cannot borrow evidence from another occurrence.
3. Transport across different local FreshUse row images retains only source-authenticated role identities, checks all four provider ports in their source graph, and does not synthesize local bounds.
4. Activation through an external Definition pair is allowed only when the exact provider receiver and role-subject rows are shared and unchanged by the same FreshUse; otherwise the same-use reciprocal pair must exist locally.
5. Ambiguous provider matches, missing source/role rows, fresh local rows and metadata collisions remain unavailable; no removal path discards a distinct prerequisite before merge.

The source-qualified falsifier is an admitted Yulang program whose generated graph loses a required role, borrows a pair from an unrelated provider/occurrence, or activates without the same-use reciprocal relation. A hand-mutated internal record alone is not a source counterexample. Distinguish code-review findings, executable correspondence and mathematical theorem claims. Do not promote the original A/B or source/native gate.

## Lanes, authority and resources

- Review lane: one fresh `compiler_referee`, isolated from R333 authorship; read-only input; one report returned in its final message. Review mode M1 is sufficient for this single internal solver artifact and its source correspondence. No second reviewer unless a distinct conformance risk appears.
- Primary lane: inspect the exact owners and adjudicate the handoff. Keep the pinned code unchanged while review runs. Do not add observational code. The Button branch-discharge route has `NO_SAFE_CODE_SLICE` until source-domain/dispatch preservation is established. A concrete in-scope review defect may be repaired by the primary only after the reviewer stops; first update the exact lease/contract, then run focused source tests and obtain delta review of changed bytes.
- No child writes, no Astra, no new semantics, no expected-output changes, no production cutover, no broad cleanup.
- Fresh envelope: 1,800 active seconds total, no R333 carryover; reviewer maximum 1,200 seconds, primary adjudication/recording reserve 600 seconds. One heavy Cargo process maximum; existing R333 checks are evidence, not repeated success criteria. Unknown legacy writers remain quarantined and consume their reservations.
- Stop at completed adjudication, a precise source-qualified obstruction, the 1,800-second cap, user STOP, or session end. Unknown reviewer cessation keeps its output lease quarantined.

## Exact writes and Git boundary

Only `/root` writes this contract, `tasks/agent-loop/current.json`, and `notes/theory/2026-10-23-r334-r333-independent-review.md`. Reviewer returns its report by message and writes no files. The R333 code, note and contract remain frozen during review. A post-review source repair requires a separate exact lease update recorded before writing; it does not authorize other source paths.

The primary owns review adjudication, compact-state/history synchronization, staging, commit and push. Stage only these explicit paths: the R334 contract, the R334 outcome note, and `tasks/agent-loop/current.json` (plus `candidate_scheme.rs` only if a concrete reviewed defect is repaired under the recorded lease). Do not stage pending question bundles. Do not rewrite history or force-push. At this sprint boundary, parent goals and all unrelated OPEN gates remain unchanged.
