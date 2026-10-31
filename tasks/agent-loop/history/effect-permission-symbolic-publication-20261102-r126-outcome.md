# R126 outcome — symbolic FormalEntry publication

Contract: `tasks/agent-loop/sprints/effect-permission-symbolic-publication-20261102-r126.md`, SHA-256 `8a999995dca10358d9a8aaf9db8a5e7b473edc0e199e9b0de3e066157e86d8cb`. Manifest: `tasks/agent-loop/sprints/effect-permission-symbolic-publication-20261102-r126-inputs-r1.json`, SHA-256 `7e47ad03d3e49f8cf711d1c46d52a106179b1c86b40cd18ce0f2fb8c172cf155`. Baseline branch `yulang3`, commit `e4570173a19ed72f6257fa391032f153ca43943d`; R39 remains pinned to `1f5835c276143537ec58ed81db96c7c108cea8e7`.

## Result

**PASS for the bounded source-native symbolic publication equations and conditional application to existing R39.** The immutable Rust audit authenticates both equations required after R125:

1. For one successful symbolic helper, `V1 = V0` for the private ordered `formal_entry_permissions` Vec from immediately before to immediately after the helper. The drain mutates context/replay/effect state; the relevant Vec's logical writes are the later permission push and checkpoint rollback truncation, neither reached between these timestamps on a successful helper path.
2. The two direct requests produce the invocation-scoped ordered provenance suffix for local slots 45 then 46. Each retained edge resolves through its FactId to the exact original typed `Term` pair, before propagation endpoint canonicalization. Canonical fact storage may deduplicate while provenance still appends one edge per admitted request. If `U == T`, the ordered term pair and FactId may be shared, but `C45 != C46` preserves two ordered edges. If `U != T`, the ordered term pairs differ. Earlier provenance remains a prefix; the result does not claim global slot uniqueness.

The existing R39 `constructed_entry_publication` application remains conditional on the reviewed R125 same-graph PRE witness and these source equations. The theorem itself does not assert drain preservation or provenance realization; the audit supplies that bounded source bridge. No new theorem, model, axiom or Lean execution was added.

## Evidence and review

- Source handoff revision 3: `tasks/agent-loop/inbox/effect-permission-symbolic-publication-r126-source.md`, SHA-256 `a6bd6db65a2d3a2c92a8adad0d501e176b9a35bd646deb4e241c31faf66f7e27`.
- Proof handoff revision 1: `tasks/agent-loop/inbox/effect-permission-symbolic-publication-r126-proof.md`, SHA-256 `36f18bb7b09e73451dce28497a83d8bb3b5ec5a951fcb4fec6a08e14b7fdca18`. It records the exact R39 theorem type and required source equations, without claiming they were available at its freeze time or newly kernel checked.
- Fresh independent compiler referee: **PASS, no remaining BLOCKING, major or minor findings**. The reviewer authenticated all eight pinned Rust/theory blobs, both handoffs and the three R125 dependencies. Revision 1's two minor findings were corrected sequentially: the `U == T` shared-FactId case and stale `apply_effect_task` locator; a final delta review confirmed revision 3's consolidated locator and unchanged pair analysis. Revision hashes are retained in the source handoff.
- Source, proof and reviewer workers are STOPPED. Requested/effective model receipts and unmeasured resource use remain as recorded by each worker; no runtime metadata or CPU/RSS usage is inferred.

## Limits and disposition

Close R126 conditionally. This does not interpret external `State.inflow`, prove the later `candidate_receiver` consumer read, establish whole-call atomicity or rollback, or close the parent soundness/effect-hygiene, principality, termination or production obligations. R121 consumer correspondence and R111's private 6 GiB verifier-resource gate remain OPEN. Rust source was not edited; compiler integration remains **NO_SAFE_CODE_SLICE** under current resources and leases.

No tests, builds, Lean execution, or source execution occurred. The primary ran `python3 tools/agent_sprint.py check`, which passed as static workflow consistency only, not as proof or independent review. No environment/storage probes, caches, worktrees, copies, dirty/quarantined source reads or source edits occurred. Continue the standing Rust/Lean goal at the next admitted source/proof seam.
