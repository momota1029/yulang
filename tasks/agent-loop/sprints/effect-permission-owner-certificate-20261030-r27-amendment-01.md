# R27 amendment 01 — disambiguate baseline binary and bind capture-time outer Owner

Sprint: EFFECT-PERMISSION-OWNER-CERTIFICATE/20261030-R27. Primary authority: Luna. This amendment preserves the goal, source domain, semantics, resource envelope, write leases, stop conditions and production boundary in revision 1.

## Evidence prompting the amendment

The two revision-1 baseline invocations both exited 101 before source entry because Cargo found three binaries and could not select one. The Rust author reports callback status 101 in 0.121s and companion status 101 in 0.019s; the competing binaries were inline_authentic_extraction, name_entry_trace and yu-playground. No source execution was attempted. No candidate compilation or runtime occurred, and no Rust source/receipt/handoff writes were made. The failure is a command-selection issue, not a source transition; preserve it as failed invocation evidence and retry only with an explicit binary selector.

The proof author inspected the pinned clean capture path. capture_template appends a final TemplateNode::Owner after saved-suffix nodes, sets its inner edge to the preceding root, then sets ResumeTemplate.root to this appended index. Saved suffixes may themselves contain other Owner nodes. Therefore `nodes[index] is Owner` alone is insufficient: a different positive index can also designate an Owner.

## Exact sequential correction

1. Inputs revision 2 changes only the two baseline Cargo commands to select `--bin yu-playground`. It pins the revision-1 failure statuses and elapsed observations. Aggregate Cargo cap remains 360 seconds; the corrected baseline retry is still before candidate source entry.
2. Schema revision 2 requires lookup coordinate equality `node_index == captured_template.root == captured_template.nodes.len() - 1`, and requires the node at that immutable coordinate to be the final appended Owner with the recorded preceding-root inner edge. The wrong-positive-index mutation must reject an alternate valid Owner index when one exists, specifically because it differs from the capture-time root coordinate. Each mutation still proves its target existed and changed an applicable record.
3. No source, expected result, dependency, theorem scope, budget, lease or production authority changes. Candidate compile/runtime remain blocked on fresh independent exact-hash ACCEPT plus separate Luna stage authorization. Lean audits remain blocked until Luna confirms baseline Cargo is stopped and grants the serialized window.

## Frozen revisions and worker gate

Base contract revision 1 remains frozen at SHA-256 `2cc9c8ae08a6fcbf98f237e6a1640ceb042a456a6beaadc448fa0a0308b431f0`. Schema r2: `tasks/agent-loop/sprints/effect-permission-owner-certificate-20261030-r27-schema-r2.json`. Inputs r2: `tasks/agent-loop/sprints/effect-permission-owner-certificate-20261030-r27-inputs-r2.json`. This amendment is a new immutable record; no prior file is rewritten. Both authors paused file writes while Luna prepared this revision. Resume only after this amendment and its schema/inputs hashes are committed/pushed, current-state leases/hashes are synchronized, and each author acknowledges the exact new hashes. The bounded baseline retry then runs serially before candidate work continues.

Conservative upper-bound charges at amendment preparation: Rust 360/1,550s; Lean 330/800s; Luna 360/3,850s. The short Cargo failures are included; no prior R26 capacity transfers. Reviewer remains 0/1,000s. No Lean/Lake process ran.
