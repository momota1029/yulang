# R230 — WorkBound snapshot covers same-owner physical fibers

Status: CLOSED_SOURCE_NATIVE_EVIDENCE; Luna solo primary, no independent review.
Branch / baseline: `research/simple-sub-intrusion` / `67b26c16b`.
Parent: unchanged computation-forwarding theorem §§1, 6–7; R71/R72 remain OPEN.

## Fixed outcome

Narrow R71's raw/canonical coverage obligation by proving from the current production source that one selected row visit enumerates every same-owner physical bound slot in its captured prefix, and that each raw slot's retained fibers are transferred to the same canonical child selected for that copy. Identify the exact remaining cross-owner scheduling premise. Do not infer arbitrary reachability or change theorem quantifiers.

## Exact evidence and implementation boundary

Read the owner merge in `crates/yu-solver/src/candidate_intrusion.rs`, the Work::Visit/Work::Bound construction and dispatch in `crates/yu-solver/src/candidate_extrusion.rs`, raw-fiber transfer in `crates/yu-solver/src/candidate_effect.rs`, and canonicalization/replay/evidence transport in `crates/yu-solver/src/candidate_context.rs`.

No production code or solver behavior is authorized by this packet. No independent reviewer or child worker is used. The only outputs are this contract, its theory receipt and `tasks/agent-loop/current.json`.

## Success evidence and falsifiers

Success requires: owner merge retains all source physical entries in the destination representative; row visit snapshots their lengths; each raw slot creates one Work::Bound with the raw source key and the canonical mapped child key; the Work::Bound transfers every fiber attached to that exact raw key; and equality canonicalization retains both raw attachment and canonical attachment. A falsifier is any omitted physical slot, source key canonicalized before raw lookup, child mapping divergence for sibling aliases, or transfer that fails to retain a relation parent/transform.

The conclusion is strictly same-owner, same-visit-prefix coverage. It does not establish that a third owner's slot is scheduled, that its downstream consumer independently requires that fiber, that all source-reachable schedules satisfy the required lineage, or that R71/R72/the parent theorem close.

## Checks and boundary

`cargo test -p yu-playground` passed on baseline 67b26c16b. This is ordinary sample/runtime evidence and is not the proof check for the code lemma. Run sprint static check, 57 tooling tests and `git diff --check` for the resulting state/artifacts. Commit/push only the exact leased files after recording the conclusion.
